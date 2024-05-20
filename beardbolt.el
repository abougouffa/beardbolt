;;; beardbolt.el --- A compiler output viewer -*- lexical-binding: t; -*-

;; Copyright (C) 2018-2021 Jay Kamat 2022 João Távora
;; Author: João Távora <joaotavora@gmail.com>
;; Version: 0.1.2
;; Keywords: compilation, tools
;; URL: https://github.com/joaotavora/beardbolt
;; Package-Requires: ((emacs "28.1"))

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU Affero General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU Affero General Public License for more details.

;; You should have received a copy of the GNU Affero General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; beardbolt is a fork of the amazing rmsbolt.el, found at
;; https://gitlab.com/jgkamat/rmsbolt, a package to provide assembly or
;; bytecode output for a source code input file.


;;; Requires:

(require 'cl-lib)
(eval-when-compile (require 'subr-x))
(require 'map)
(require 'compile)
(require 'disass)
(require 'json)
(require 'color)
(require 'pulse)

;;; Code:
(defgroup beardbolt nil
  "beardbolt customization options"
  :group 'applications)

(defmacro beardbolt--defoption (sym &rest whatever)
  `(progn (defcustom ,sym ,@whatever) (put ',sym 'beardbolt--option t)))

(beardbolt--defoption beardbolt-command nil
                      "The base command to run beardbolt from."
                      :type 'string :safe (lambda (v) (or (listp v) (stringp v))))
(beardbolt--defoption beardbolt-disassemble nil
                      "Non-nil to assemble then disassemble an output binary."
                      :type 'boolean :safe 'booleanp)
(beardbolt--defoption beardbolt-asm-format 'att
                      "Which output assembly format to use.
Passed directly to compiler or disassembler."
                      :type 'string :safe (lambda (v) (or (null v) (symbolp v) (stringp v))))
(beardbolt--defoption beardbolt-preserve-directives nil
                      "Non-nil to keep assembly directives."
                      :type 'boolean :safe 'booleanp)
(beardbolt--defoption beardbolt-preserve-unused-labels nil
                      "Non-nil to keep unused labels."
                      :type 'boolean :safe 'booleanp)
(beardbolt--defoption beardbolt-preserve-library-functions nil
                      "Non-nil to keep functions with no code related to current file."
                      :type 'boolean :safe 'booleanp)
(beardbolt--defoption beardbolt-preserve-comments nil
                      "Non-nil to filter comment-only lines."
                      :type 'boolean :safe 'booleanp)
(beardbolt--defoption beardbolt-demangle t
                      "Non-nil to attempt to demangle the resulting assembly."
                      :type 'boolean :safe 'booleanp)
(beardbolt--defoption beardbolt-execute nil
                      "Non-nil to run resulting program with these arguments."
                      :type 'string :safe (lambda (v) (or (null v) (eq t v) (stringp v))))
(beardbolt--defoption beardbolt-ccj-extra-flags nil
                      "Extra flags for compilation command devined from compile_commands.json."
                      :type 'string :safe (lambda (v) (or (null v) (stringp v))))
(beardbolt--defoption beardbolt-shuffle-rainbow nil
                      "Choose less pretty, but potentially more contrasting rainbow colors."
                      :type 'boolean :safe 'booleanp)

(defface beardbolt-current-line-face
  '((t (:weight bold :inherit highlight)))
  "Face to fontify the current line for showing matches.")

(defvar-local beardbolt--asm-buffer nil)
(defvar-local beardbolt--source-buffer nil)
(defvar-local beardbolt--compile-spec nil)
(defvar-local beardbolt--declared-output nil)
(defvar-local beardbolt--dump-file nil "Temporary file")
(defvar-local beardbolt--line-mappings nil
  "List where of asm-to-source mappings.
Each element is ((ASM-BEG-LINE . ASM-END-LINE) . SRC-LINE).")
(defvar-local beardbolt--rainbow-overlays nil "Rainbow overlays.")

(defun beardbolt--asm-buffer (src-buffer)
  "Get/create asm buffer for current source file."
  (with-current-buffer src-buffer
    (or (and (buffer-live-p beardbolt--asm-buffer)
             (equal (buffer-name beardbolt--asm-buffer) "*beardbolt-asm*")
             beardbolt--asm-buffer)
        (setq beardbolt--asm-buffer
              (with-current-buffer
                  (get-buffer-create "*beardbolt-asm*")
                (current-buffer))))))

(defvar beardbolt-compile-delay 0.6
  "Time in seconds to delay before recompiling if there is a change.
If nil, auto-recompilation is off.")

(defvar beardbolt--shell "bash"
  "Which shell to prefer if available.
Used to work around inconsistencies in alternative shells.")

(defun beardbolt--sandbox-dir ()
  (let ((d (expand-file-name "beardbolt-sandbox" user-emacs-directory)))
    (make-directory d 'parents)
    d))

(defvar beardbolt-dir (file-name-directory load-file-name)
  "The directory which beardbolt is installed to.")

(defvar-local beardbolt-objdump-binary "objdump"
  "A binary to use for objdumping when using `beardbolt-disassemble'.
Useful if you have multiple objdumpers and want to select between them")

;;;; Regexes

(defvar beardbolt-label-start  "^\\([^:]+\\): *\\(?:#\\|$\\)\\(?:.*\\)")


(defvar beardbolt-defines-global (rx bol (0+ space) ".glob"
                                     (opt "a") "l" (0+ space)
                                     (group (any ".a-zA-Z_")
                                            (0+ (any "a-zA-Z0-9$_.")))))
(defvar beardbolt-label-reference (rx "." (any "a-zA-Z_")
                                      (0+
                                       (any "a-zA-Z0-9$_."))))
(defvar beardbolt-has-opcode (rx bol (1+ space)
                                 (1+ (any "a-zA-Z"))))

(defvar beardbolt-defines-function-or-object (rx bol
                                                 (0+ space) ".type"
                                                 (0+ space)
                                                 (group (0+ any)) "," (0+ space) (any "@%")))
(defvar beardbolt-data-defn (rx bol (0+ space) "."
                                (group (or "string" "asciz" "ascii"
                                           (and
                                            (optional (any "1248")) "byte")
                                           "short" "word" "long" "quad" "value" "zero"))))

(defvar beardbolt-endblock (rx "." (or "cfi_endproc" "data" "text" "section")))
(defvar beardbolt-comment-only (rx bol (0+ space) (or (and (or (any "#@;") "//"))
                                                      (and "/*" (0+ any) "*/"))
                                   (0+ any) eol))
(defvar beardbolt-disass-line (rx bol
                                  (group "/" (1+ (not (any ":")))) ":"
                                  (group (1+ num))
                                  (0+ any)))
(defvar beardbolt-disass-label (rx bol (group (1+ (any digit "a-f")))
                                   (1+ space) "<"
                                   (group (1+ (not (any ">")))) ">:" eol))
(defvar beardbolt-disass-dest (rx (0+ any) (group (1+ (any digit "a-f")))
                                  (1+ space) "<" (group (1+ (not (any ">")))) ">" eol))

(defvar beardbolt-disass-opcode (rx bol (0+ space) (group (1+ (any digit "a-f")))
                                    ":" (0+ space)
                                    (group (1+
                                            (repeat 2
                                                    (any digit "a-f"))
                                            (opt " ")))
                                    (0+ space)
                                    (group (0+ any))))
(defvar beardbolt-source-file-hint (rx bol (0+ space) ".file" (1+ space)
                                       (group (1+ digit)) (1+ space) ?\"
                                       (group (1+ (not (any ?\")))) ?\"
                                       (opt (1+ space) ?\"
                                            (group (1+ (not (any ?\")))) ?\")
                                       (0+ any)))
(defvar beardbolt-source-tag (rx bol (0+ space) ".loc" (1+ space)
                                 (group (1+ digit)) (1+ space)
                                 (group (1+ digit))
                                 (0+ any)))
(defvar beardbolt-source-stab (rx bol (0+ any) ".stabn" (1+ space)
                                  (group (1+ digit)) ",0,"
                                  (group (1+ digit)) "," (0+ any)))

(defun beardbolt--split-rm-single (cmd flag &optional test)
  "Remove a single FLAG from CMD.  Test according to TEST."
  (mapconcat #'identity (cl-remove flag (split-string cmd)
                                   :test (or test #'string=))
             " "))

(defun beardbolt--split-rm-double (cmd flag)
  "Remove a FLAG and subsequent arg from CMD."
  (cl-loop while split with split = (split-string cmd)
           for i from 0
           for probe = (car split)
           if (string= probe flag) do (setq split (cddr split))
           else
           concat (and (cl-plusp i) " ")
           and concat probe and do (setq split (cdr split))))

(cl-defun beardbolt--c/c++-setup (&key base-cmd language)
  "Get compile specs for gcc/clang."
  (let* ((modified-p (buffer-modified-p))
         (source-hint (if modified-p "<stdin>" (buffer-file-name)))
         (base-command (ensure-list (or beardbolt-command
                                        (beardbolt--guess-from-ccj)
                                        base-cmd)))
         (cc (car (split-string (car base-command)))))
    (cl-labels ((f (x) (expand-file-name x (beardbolt--sandbox-dir)))
                (compile (in out) `(,@base-command
                                    "-g1"
                                    "-S" ,(format "-masm=%s" beardbolt-asm-format)
                                    "-o" ,out
                                    ,@(if modified-p
                                          `("-x" ,language "-" "<" ,in)
                                        `(,(buffer-file-name)))))
                (assemble (in out) `("&&" ,cc "-c" ,in "-o" ,out))
                (link     (in out) `("&&" ,cc ,in      "-o" ,out))
                (execute  (in)     `("&& (" ,in
                                     ,(if (stringp beardbolt-execute) beardbolt-execute "")
                                     "|| true )"))
                (disassemble (in out) `("&&" ,beardbolt-objdump-binary "-d"
                                        ,in "--insn-width=16" "-l"
                                        ,(when beardbolt-asm-format (format "-M %s" beardbolt-asm-format))
                                        ">" ,out)))
      `((:compile
         ,(lambda (dump-file)
            (cons
             `(,(compile dump-file (f "beardbolt.s"))
               ,@(when beardbolt-execute
                  `(,(assemble (f "beardbolt.s") (f "beardbolt.o"))
                    ,(link     (f "beardbolt.o") (f "beardbolt.out"))
                    ,(execute  (f "beardbolt.out")))))
             (f "beardbolt.s")))
         ,(lambda (_dump-file) (beardbolt--process-asm source-hint)))
        (:compile-assemble-disassemble
         ,(lambda (dump-file)
            (cons
             `(,(compile     dump-file         (f "beardbolt.s"))
               ,(assemble    (f "beardbolt.s") (f "beardbolt.o"))
               ,(disassemble (f "beardbolt.o") (f "beardbolt.o.disass"))
               ,@(when beardbolt-execute
                  `(,(link    (f "beardbolt.o") (f "beardbolt.out"))
                    ,(execute (f "beardbolt.out")))))
             (f "beardbolt.o.disass")))
         ,(lambda (_dump-file)
            (beardbolt--process-disassembled-lines source-hint)))))))

(cl-defun beardbolt--rust-setup () "Get compile specs for rustc"
          (let* ((base (ensure-list (or beardbolt-command "rustc"))))
            (cl-labels ((f (x) (expand-file-name x (beardbolt--sandbox-dir)))
                        (disassemble (in out) `("&&" ,beardbolt-objdump-binary "-d"
                                                ,in "--insn-width=16" "-l"
                                                ,(when beardbolt-asm-format (format "-M %s" beardbolt-asm-format))
                                                ">" ,out))
                        (link (in out)
                          `(,@base "-C debuginfo=1" "--emit" "link" ,in "-o" ,out))
                        (compile (in out)
                          `(,@base "-C debuginfo=1" "--emit" "asm" ,in
                            ,(when beardbolt-asm-format (format
                                                         "-Cllvm-args=--x86-asm-syntax=%s"
                                                         beardbolt-asm-format))
                            "-o" ,out)))
              `((:compile
                 ,(lambda (dump-file)
                    (cons
                     (compile dump-file (f "beardbolt.s"))
                     (f "beardbolt.s")))
                 ,#'beardbolt--process-asm)
                (:compile-assemble-disassemble
                 ,(lambda (dump-file)
                    (cons
                     `(,(link        dump-file         (f "beardbolt.o"))
                       ,(disassemble (f "beardbolt.o") (f "beardbolt.o.disass")))
                     (f "beardbolt.o.disass")))
                 ,#'beardbolt--process-disassembled-lines)))))

(defvar beardbolt-languages
  `((c-mode    ,#'beardbolt--c/c++-setup :base-cmd "gcc" :language "c")
    (c++-mode  ,#'beardbolt--c/c++-setup :base-cmd "g++" :language "c++")
    (rust-mode ,#'beardbolt--rust-setup))
  "Alist of (MAJOR-MODE SETUP . SETUP-ARGS).

SETUP is a function called with `apply' on SETUP-ARGS.

It returns a list (SPEC ...) where SPEC is (WHAT CMD-FN PRETTY-FN).

WHAT is a symbol `:compile' or `:compile-assemble-disassemble'.

CMD-FN is a function taking IN-FILE, name of the temp file with
the current buffer's content, and returning a cons cell (CMD
. OUT-FILE).  CMD is a string or a tree of strings.  When
flattened and joined with whitespace, it represents a shell
command to produce a file named OUT-FILE, whose contents are
inserted into the asm buffer.

PRETTY-FN is a function taking IN-FILE, to run in the asm buffer
where OUT-FILE's contents are freshly inserted. It may clean up
some parts of the buffer and setup a buffer-local value of
`beardbolt--line-mappings' (which see).")

(defmacro beardbolt--get (sym) `(buffer-local-value ',sym beardbolt--source-buffer))

(defmacro beardbolt--sweeping (&rest forms)
  (declare (indent 0)
           (debug (&rest (form &rest form))))
  (let ((lbp (cl-gensym "lbp-")) (lep (cl-gensym "lep-"))
        (preserve-directives (cl-gensym "preserve-directives-"))
        (linum (cl-gensym "linum-")))
    `(let ((,preserve-directives (beardbolt--get beardbolt-preserve-directives))
           (,linum 1))
      (goto-char (point-min))
      (while (not (eobp))
       (let ((,lbp (line-beginning-position)) (,lep (line-end-position)))
        (cl-macrolet ((match (&rest res)
                        `(cl-loop for re in ,(cons 'list res)
                          thereis (re-search-forward re ,',lep t)))
                      (update-lep () `(setq ,',lep (line-end-position)))
                      (asm-linum () ',linum)
                      (preserve () `(progn
                                      (forward-line 1)
                                      (setq ,',linum (1+ ,',linum)))))
         (pcase (cond ,@forms)
          (:preserve (preserve))
          (:kill (delete-region ,lbp (1+ ,lep)))
          (_
           (if ,preserve-directives (preserve)
            (delete-region ,lbp (1+ ,lep)))))))))))

(defun beardbolt--register-mapping (source-linum l)
  (let ((current-chunk (car beardbolt--line-mappings)))
    (if (and (eq source-linum (cdr current-chunk))
             (eq l (1+ (cdar current-chunk))))
        (setf (cdar current-chunk) l)
      (push (cons (cons l l) source-linum)
            beardbolt--line-mappings))))

(cl-defun beardbolt--process-disassembled-lines (main-file-name)
  (let* ((func nil) (source-linum nil))
    (cl-flet ((beardbolt--user-func-p (func)
                (let* ((regexp (rx bol (or (and "__" (0+ any))
                                           (and "_" (or "init" "start" "fini"))
                                           (and (opt "de") "register_tm_clones")
                                           "call_gmon_start"
                                           "frame_dummy"
                                           (and ".plt" (0+ any)))
                                   eol)))
                  (if regexp (not (string-match-p regexp func)) t))))
      (beardbolt--sweeping
        ((match beardbolt-disass-line)
         (setq source-linum (and (equal (file-name-base main-file-name) ;; brittle
                                        (file-name-base (match-string 1)))
                                 (string-to-number (match-string 2))))
         :kill)
        ((match beardbolt-disass-label)
         (setq func (match-string 2))
         (when (beardbolt--user-func-p func) (replace-match (concat func ":")))
         :preserve)
        ((and func (not (beardbolt--user-func-p func)))
         :kill)
        ((match beardbolt-disass-opcode)
         (when source-linum
           (beardbolt--register-mapping source-linum (asm-linum)))
         (replace-match (concat (match-string 1) "\t" (match-string 3)))
         :preserve)))))

(defun beardbolt--process-asm (main-file-name)
  (let* ((used-labels (obarray-make))
         (routines (make-hash-table :test #'equal))
         main-file-tag
         main-file-routines
         source-linum
         current-routine
         reachable-label
         (preserve-comments (beardbolt--get beardbolt-preserve-comments))
         (preserve-unused-labels (beardbolt--get beardbolt-preserve-unused-labels))
         (preserve-library-functions (beardbolt--get beardbolt-preserve-library-functions)))
    (beardbolt--sweeping ; first pass
      ((not (eq (char-after) ?\t))
       (cond ((match beardbolt-label-start)
              (unless (eq :notfound (gethash (match-string 1) routines :notfound))
                (setq current-routine (match-string 1)))
              :preserve)
             (t :kill)))
      (t
       (cond ((and current-routine (match beardbolt-has-opcode))
              (while (match beardbolt-label-reference)
                (push (match-string 0) (gethash current-routine routines)))
              :preserve)
             ((and (not preserve-comments) (match beardbolt-comment-only))
              :kill)
             ((match beardbolt-defines-global beardbolt-defines-function-or-object)
              (puthash (match-string 1) nil routines))
             ((and (match beardbolt-source-file-hint)
                   (equal (or (match-string 3) (match-string 2))
                          main-file-name))
              (setq main-file-tag (match-string 1)))
             ((match beardbolt-source-tag)
              (when (and current-routine
                         (equal (match-string 1) main-file-tag))
                (push current-routine main-file-routines))
              :preserve)
             ((match beardbolt-endblock) (setq current-routine nil) :preserve)
             (t :preserve))))
    (dolist (mfr (if preserve-library-functions
                     (hash-table-keys routines)
                   main-file-routines))
      (intern mfr used-labels)
      (dolist (callee (gethash mfr routines)) (intern callee used-labels)))
    (beardbolt--sweeping ; second pass
      ((not (eq (char-after) ?\t))
       (when (match beardbolt-label-start)
         (cond
          ((intern-soft (match-string 1) used-labels)
           (setq reachable-label (match-string 1))
           :preserve)
          (t
           (if preserve-unused-labels :preserve :kill)))))
      (t
       (cond ((and (match beardbolt-data-defn) reachable-label)
              :preserve)
             ((and (match beardbolt-has-opcode) reachable-label)
              (when source-linum (beardbolt--register-mapping source-linum (asm-linum)))
              :preserve)
             ((match beardbolt-source-tag)
              (setq source-linum
                    (and (equal (match-string 1) main-file-tag)
                         (string-to-number (match-string 2)))))
             ((match beardbolt-source-stab)
              (pcase (string-to-number (match-string 1))
                ;; http://www.math.utah.edu/docs/info/stabs_11.html
                (68 (setq source-linum (string-to-number (match-string 2))))
                ((or 100 132) (setq source-linum nil))))
             ((match beardbolt-endblock)
              (setq reachable-label nil)))))))

(cl-defun beardbolt--rainbowize (src-buffer)
  (beardbolt-clear-rainbow-overlays)
  (let* ((background-hsl
          (ignore-errors
            (apply #'color-rgb-to-hsl (color-name-to-rgb (face-background 'default)))))
         all-ovs
         (idx 0)
         total
         (shuffle (buffer-local-value 'beardbolt-shuffle-rainbow src-buffer))
         (ht (make-hash-table)))
    (cl-loop initially (goto-char (point-min))
             with current-line = 1
             for (asm-region . src-line) in beardbolt--line-mappings
             for (begl . endl) = asm-region
             do (push (cons (progn
                              (forward-line (- begl current-line))
                              (line-beginning-position))
                            (progn
                              (forward-line (- endl begl))
                              (setq current-line endl)
                              (line-end-position)))
                      (gethash src-line ht)))
    ;; The 1+ helps us keep our hue distance from the actual
    ;; background color
    (setq total (1+ (hash-table-count ht)))
    (unless background-hsl (cl-return-from beardbolt--rainbowize nil))
    (maphash
     (lambda (src-line asm-pos-regions)
       (when (not (zerop src-line))
         (cl-loop
          with i = (if shuffle
                       (mod (* 27 (cl-incf idx)) total)
                     (cl-incf idx))
          with bright-hsl =(list (mod (+ (cl-first background-hsl)
                                         (/ i (float total)))
                                      1)
                                 (min (max (cl-second background-hsl)
                                           0.25)
                                      0.8)
                                 (min (max (cl-third background-hsl)
                                           0.25)
                                      0.8))
          with muted-hsl = (list (car bright-hsl)
                                 (/ (cadr bright-hsl) 2.0)
                                 (caddr bright-hsl))
          with color = (apply #'color-rgb-to-hex (apply #'color-hsl-to-rgb bright-hsl))
          with muted-color = (apply #'color-rgb-to-hex (apply #'color-hsl-to-rgb muted-hsl))
          for (beg . end) in asm-pos-regions
          for asm-ov = (make-overlay beg end)
          do
          (overlay-put asm-ov 'priority 0)
          (push asm-ov all-ovs)
          (overlay-put asm-ov 'face `(:background ,color))
          (overlay-put asm-ov 'beardbolt-rainbow-face `(:background ,color))
          (overlay-put asm-ov 'beardbolt-muted-face `(:background ,muted-color))
          (overlay-put asm-ov 'beardbolt 'asm)
          collect asm-ov into this-lines-asm-overlays
          finally
          (with-current-buffer src-buffer
            (save-excursion
              (goto-char (point-min))
              (forward-line (1- src-line))
              (let* ((ov (make-overlay (line-beginning-position)
                                       (1+ (line-end-position))))
                     (group (cons ov this-lines-asm-overlays)))
                (overlay-put ov 'beardbolt-related-overlays group)
                (dolist (o group)
                  (overlay-put o 'beardbolt-related-overlays group))
                (overlay-put ov 'face `(:background ,color))
                (overlay-put ov 'beardbolt-rainbow-face `(:background ,color))
                (overlay-put ov 'beardbolt-muted-face `(:background ,muted-color))
                (overlay-put ov 'beardbolt t)
                (push ov all-ovs)))))))
     ht)
    (mapc #'delete-overlay beardbolt--rainbow-overlays)
    (setq beardbolt--rainbow-overlays all-ovs)))

(cl-defmacro beardbolt--when-live-buffer (buf &rest body)
  "Check BUF live, then do BODY in it." (declare (indent 1) (debug t))
  (let ((b (cl-gensym)))
    `(let ((,b ,buf)) (if (buffer-live-p ,b) (with-current-buffer ,b ,@body)))))

(defun beardbolt-clear-rainbow-overlays ()
  "Clear rainbow from the source file and asm output."
  (interactive)
  (let ((output-buffer (if (eq major-mode 'beardbolt--asm-mode)
                           (current-buffer)
                         beardbolt--asm-buffer)))
    (beardbolt--when-live-buffer output-buffer
      (beardbolt--when-live-buffer beardbolt--source-buffer
        (save-restriction
          (widen)
          (cl-loop for o in (overlays-in (point-min) (point-max))
                   when (overlay-get o 'beardbolt) do (delete-overlay o)))))
    (mapc #'delete-overlay beardbolt--rainbow-overlays)
    (setq beardbolt--rainbow-overlays nil)))

;;;;; Handlers
(cl-defun beardbolt--handle-finish-compile (compilation-buffer str)
  "Finish hook for compilations.  Runs in buffer COMPILATION-BUFFER.
Argument STR compilation finish status."
  (let* ((dump-file-name beardbolt--dump-file)
         (src-buffer beardbolt--source-buffer)
         (origin-window (or (get-buffer-window src-buffer)
                            (selected-window)))
         (compile-spec beardbolt--compile-spec)
         (declared-output beardbolt--declared-output)
         (asm-buffer (beardbolt--asm-buffer src-buffer)))
    (delete-file dump-file-name)
    (with-current-buffer asm-buffer
      (beardbolt--asm-mode)
      (setq beardbolt--source-buffer src-buffer)
      (let* ((inhibit-modification-hooks t)
             (inhibit-read-only t)
             (window
              (with-selected-window origin-window
                (display-buffer asm-buffer '(nil (inhibit-same-window . t))))))
        (erase-buffer)
        (cond
         ((string-match "^finished" str)
          (mapc #'delete-overlay (overlays-in (point-min) (point-max)))
          (insert-file-contents declared-output)
          (setq beardbolt--line-mappings nil)
          (save-excursion (funcall (cadr compile-spec) dump-file-name))
          (setq beardbolt--line-mappings (reverse beardbolt--line-mappings))
          (when (beardbolt--get beardbolt-demangle)
            (shell-command-on-region (point-min) (point-max) "c++filt"
                                     (current-buffer) 'no-mark))
          (beardbolt--rainbowize src-buffer))
         (t
          (insert "<Compilation failed>")))
        (unless (or (string-match "^interrupt" str)
                    (get-buffer-window compilation-buffer)
                    (and (string-match "^finished" str)
                         (not (beardbolt--get beardbolt-execute))))
          (with-selected-window window
            (let ((cwindow
                   (display-buffer compilation-buffer
                                   `((display-buffer-below-selected)))))
              (set-window-dedicated-p cwindow 'beardbolt-dedication))))))))

(defun beardbolt--compilation-buffer (&rest _)
  (get-buffer-create "*beardbolt-compilation*"))

;;;;; UI Functions
(defun beardbolt-compile (lang-desc)
  "Run beardbolt on current buffer for LANG-DESC.
LANG-DESC is an element of `beardbolt-languages'.  Interactively,
determine LANG from `major-mode'."
  (interactive (list (assoc major-mode beardbolt-languages)))
  (beardbolt--maybe-stop-running-compilation)
  (mapatoms (lambda (s) (when (get s 'beardbolt--option) (kill-local-variable s))))
  (cl-letf (((symbol-function 'hack-local-variables-confirm)
             (lambda (_all-vars unsafe-vars risky-vars &rest _)
               (when unsafe-vars
                 (message "[beardbolt] Some variables unsafe %s" unsafe-vars))
               (when risky-vars
                 (message "[beardbolt] Some variables risky %s" risky-vars)))))
    (hack-local-variables))
  (let* ((dump-file (make-temp-file "beardbolt-dump-" nil
                                    (concat "." (file-name-extension buffer-file-name))))
         (src-buffer (current-buffer))
         (specs (apply (cadr lang-desc) (cddr lang-desc)))
         (spec (alist-get
                (if beardbolt-disassemble :compile-assemble-disassemble :compile)
                specs))
         (command-and-declared-output (funcall (car spec) dump-file))
         (cmd (car command-and-declared-output))
         (cmd (mapconcat
               (lambda (s) (if (stringp s) s
                             (mapconcat #'identity (flatten-list s) " ")))
               (ensure-list cmd) " \\\n")))
    (let ((inhibit-message t))
      (write-region (point-min) (point-max) dump-file))
    (with-current-buffer ; With compilation buffer
        (let ((shell-file-name (or (executable-find beardbolt--shell)
                                   shell-file-name))
              (compilation-auto-jump-to-first-error t))
          ;; TODO should this be configurable?
          (compilation-start cmd nil #'beardbolt--compilation-buffer))
      ;; Only jump to errors, skip over warnings
      (setq-local compilation-skip-threshold 2)
      (setq-local compilation-always-kill t)
      (setq-local inhibit-message t)
      (add-hook 'compilation-finish-functions #'beardbolt--handle-finish-compile nil t)
      (setq beardbolt--source-buffer src-buffer)
      (setq beardbolt--compile-spec spec)
      (setq beardbolt--dump-file dump-file)
      (setq beardbolt--declared-output (cdr command-and-declared-output)))))

(defun beardbolt--maybe-stop-running-compilation ()
  (let ((buffer (beardbolt--compilation-buffer)))
    (when-let ((proc (get-buffer-process buffer)))
      (set-process-query-on-exit-flag proc nil)
      (interrupt-process proc))))

;;;; Keymap
(defvar beardbolt-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-c") #'beardbolt-compile)
    (define-key map (kbd "C-c C-d") #'beardbolt-clear-rainbow-overlays)
    map)
  "Keymap for function `beardbolt-mode'.")

;;;;; Starter Definitions

(defvar beardbolt-starter-files
  '(("c++" . "beardbolt.cpp")
    ("c" . "beardbolt.c")
    ("rust" . "beardbolt.rs")))

;;;###autoload
(defun beardbolt-starter (lang-name)
  "Setup new sandbox file for experiments.
With prefix argument, choose from starter files in `beardbolt-starter-files'."
  (interactive
   (list (if current-prefix-arg
             (completing-read "Language: " beardbolt-starter-files nil t)
           (caar beardbolt-starter-files))))
  (let* ((starter-file-name (cdr (assoc lang-name beardbolt-starter-files)))
         (base (file-name-base starter-file-name))
         (ext (file-name-extension starter-file-name))
         (sandbox-file
          (expand-file-name (concat base "-"
                                    (format-time-string "%FT%T%z")
                                    "." ext)
                            (beardbolt--sandbox-dir)))
         (src-file-name
          (when beardbolt-dir
            (expand-file-name starter-file-name
                              (expand-file-name "starters/" beardbolt-dir))))
         (src-file-exists (when src-file-name
                            (file-exists-p src-file-name))))
    (if (not src-file-exists)
        (error "Could not find starter files!")
      (unless (file-exists-p sandbox-file)
        (copy-file src-file-name sandbox-file))
      (find-file sandbox-file)
      (beardbolt-mode 1))))

(defun beardbolt--recenter-maybe (ov)
  (beardbolt--when-live-buffer (overlay-buffer ov)
    (cl-loop with pos = (overlay-start ov)
             for w in (cl-remove-if (lambda (w)
                                      (and (>= pos (* 1.1 (window-start w)))
                                           (<= pos (* 0.9 (window-end w)))))
                                    (get-buffer-window-list))
             unless (eq w (selected-window))
             do (set-window-point w pos)
             (with-selected-window w (recenter)))))

(defvar beardbolt--currently-synched-overlays nil)

(defun beardbolt--synch-relation-overlays ()
  (let* ((at-point (overlays-at (point)))
         (all-ovs (if (eq major-mode 'beardbolt--asm-mode)
                      beardbolt--rainbow-overlays
                    (and beardbolt--asm-buffer
                         (buffer-local-value 'beardbolt--rainbow-overlays beardbolt--asm-buffer))))
         (ov (cl-find-if (lambda (ov) (overlay-get ov 'beardbolt-rainbow-face))
                         at-point)))
    (cond ((and ov (not (member ov beardbolt--currently-synched-overlays)))
           (dolist (o all-ovs)
             (overlay-put o 'face (overlay-get o 'beardbolt-muted-face)))
           (setq beardbolt--currently-synched-overlays
                 (overlay-get ov 'beardbolt-related-overlays))
           (setq beardbolt--currently-synched-overlays
                 (cl-sort beardbolt--currently-synched-overlays #'< :key #'overlay-start))
           (dolist (o beardbolt--currently-synched-overlays)
             (overlay-put o 'face 'beardbolt-current-line-face))
           (let* ((other-buffer-overlays
                   (cl-remove (current-buffer)
                              beardbolt--currently-synched-overlays
                              :key #'overlay-buffer))
                  (recenter-target (car other-buffer-overlays))
                  (pulse-delay 0.01)
                  (asm-overlays
                   (cl-remove-if-not (lambda (ov)
                                       (eq 'asm (overlay-get ov 'beardbolt)))
                                     beardbolt--currently-synched-overlays)))
             (if (memq recenter-target asm-overlays)
                 (message "[beardbolt] maps to %s asm regions."
                          (length asm-overlays))
               (message "[beardbolt] asm region %s/%s for source line %s."
                        (1+ (cl-position ov asm-overlays))
                        (length asm-overlays)
                        (with-current-buffer (overlay-buffer recenter-target)
                          (line-number-at-pos (overlay-start recenter-target)))))
             (beardbolt--recenter-maybe recenter-target)
             (pulse-momentary-highlight-overlay recenter-target
                                                'beardbolt-current-line-face)))
          ((not ov)
           (dolist (o all-ovs)
             (overlay-put o 'face (overlay-get o 'beardbolt-rainbow-face)))
           (setq beardbolt--currently-synched-overlays nil)))))

(defvar beardbolt--change-timer nil)

(defun beardbolt--after-change (&rest _)
  (beardbolt-clear-rainbow-overlays)
  (when beardbolt-compile-delay
    (when (timerp beardbolt--change-timer) (cancel-timer beardbolt--change-timer))
    (setq beardbolt--change-timer
          (run-with-timer beardbolt-compile-delay nil #'beardbolt-compile
                          (assoc major-mode beardbolt-languages)))))

(defun beardbolt--guess-from-ccj ()
  (if-let* ((ccj-basename "compile_commands.json")
            (ccj-dir (locate-dominating-file default-directory ccj-basename))
            (ccj-file (expand-file-name ccj-basename ccj-dir))
            (ccj (with-temp-buffer
                   (insert-file-contents ccj-file)
                   (goto-char (point-min))
                   (json-parse-buffer :object-type 'plist)))
            (cmd (cl-loop for e across ccj
                          for file = (plist-get e :file)
                          when (equal file buffer-file-name)
                          return (plist-get e :command)))
            (cmd (beardbolt--split-rm-double cmd "-o"))
            (cmd (beardbolt--split-rm-double cmd "-c"))
            (cmd (beardbolt--split-rm-single cmd "-flto" #'string-prefix-p)))
      (list cmd beardbolt-ccj-extra-flags)))

;;;###autoload
(define-minor-mode beardbolt-mode
  "Toggle `beardbolt-mode'.  May be enabled by user in source buffer."
  :global nil :lighter " ⚡" :keymap beardbolt-mode-map
  (cond
   (beardbolt-mode
    (add-hook 'after-change-functions #'beardbolt--after-change nil t)
    (add-hook 'post-command-hook #'beardbolt--synch-relation-overlays nil t))
   (t
    (remove-hook 'after-change-functions #'beardbolt--after-change t)
    (remove-hook 'post-command-hook #'beardbolt--synch-relation-overlays t))))

(define-derived-mode beardbolt--asm-mode asm-mode "⚡asm ⚡"
  "Toggle `bearbolt--output-mode', internal mode for asm buffers."
  (add-hook 'kill-buffer-hook #'beardbolt-clear-rainbow-overlays nil t)
  (add-hook 'post-command-hook #'beardbolt--synch-relation-overlays nil t)
  (setq truncate-lines t)
  (read-only-mode t)
  (buffer-disable-undo)
  (local-set-key (kbd "q") 'quit-window))

(provide 'beardbolt)

;;; beardbolt.el ends here
;; Local Variables:
;; read-symbol-shorthands: (("beardbolt-" . "beardbolt-"))
;; End:
