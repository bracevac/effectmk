#lang racket

;; Abstract machine version in the style of Hillerström and Lindley '16:

(define (extend-env env name value)
  `((,name . ,value) . ,env))

(define (lookup env name [noerror #f])
  (let ((binding (assoc name env)))
    (if binding
      (cdr binding)
      (if noerror
	  #f
	  (error 'lookup (format "unbound variable: ~s" name))))))

(define ((not-keyword? env) head)
  (or (not (symbol? head)) (assoc head env)))

(define (tagged? tag d) (and (vector? d) (eq? tag (vector-ref d 0))))
(define (value datum) `#(value ,datum))
(define (value? d) (tagged? 'value d))
(define (value-datum d) (vector-ref d 1))

(define (closure-val lam env) (value `('closure ,lam ,env)))

;;a handler h has exactly one return clause and a list of effect handling clauses
(define handler (lambda (#:return [return '(lambda (x) x)] [clauses '()])
		  `('handler ,return ,clauses)))

;;handler closure chi
(define (hclosure h env) `('hclosure ,h ,env))

(define (hclause-lookup clauses op) (lookup clauses op #t))

;;a pure continuation frame (pframe) θ
;;a pure continuation σ is a list (stack) (θ ...)
(define (pframe env x exp) `('pframe ,env ,x ,exp))

;;a continuation frame (cframe) δ consists of a pure continuation θ and a handler closure chi
;;a continuation κ is a list (stack) (δ ...)
;;in the interpreted language, we tag κ with 'cont to disambiguate
(define (cframe σ chi) `('cframe ,σ ,chi))

(define (cont-val κ) `('cont κ))

;;the identity continuation
(define κ0 (list (cframe '() (hclosure (handler) '()))))

;;a standard machine configuration
(define (config exp env κ)
  `('config ,exp ,env ,κ))

;;a machine configuration for an unhandled operation
(define (hconfig exp env κ κop)
  `('hconfig ,exp ,env ,κ ,κop))

(define (exp->conf exp)
  (config exp '() κ0))

(define (conf->exp) '()) ;TODO

(define (interp-value valexp env)
  (match valexp
    (#t (value #t))
    (#f (value #f))
    ((? number? x) (value x))
    ((? symbol? x) (value (lookup env x)))
    (`(lambda (,x) ,body) (closure-val exp env))
    (`('cont ,κ) (cont-val κ))
    ;TODO: lists, records, sums?
    ))

(define (push-θ κ θ)
  (match κ
    (`( ('cframe ,σ ,chi) . ,κ2)
     (cons (cframe (cons θ σ) chi ) κ2))))

(define (push-δ κ δ) (cons δ κ))

(define (step conf) ;;TODO: missing value side conditions
  (match conf
    ;;application
    (`('config (,val1 ,val2) ,γ ,κ)
      (match (interp-value val1 γ)
	(`('value ('closure (lambda (,x) ,body) ,γ2))
	 (config body (extend-env γ2 x (interp-value val2 γ)) κ))
	(`('value ('cont ,κ2))
	 (config `(return ,val2) γ (append κ2 κ)))))

    ;;let binding
    (`('config (let (,x ,exp1) ,exp2) ,γ ,κ)
      (config exp1 γ (push-θ κ (pframe γ x exp2))))

    ;;return from let binding
    (`('config (return ,val) ,γ (('cframe (('pframe ,γ2 ,x ,exp) . ,σ) ,chi) . ,κ))
      (config exp (extend-env γ2 x (interp-value (value val) γ)) (push-δ κ (cframe σ chi))))

    ;;apply handler
    (`('config (handle ,body ,h) ,γ ,κ)
      (config body γ (push-δ (cframe '() (hclosure h γ)))))

    ;;return to handler
    (`('config (return ,val) ,γ (('cframe () ('hclosure ('handler (lambda (,x) ,retbody) _) ,γ2)) . ,κ))
      (config  retbody (extend-env γ2 x (interp-value (value val) γ)) κ))

    ;;return to top
    (`('config (return ,val) ,γ ())
      (interp-value val γ))

    ;;op invocation: start
    (`('config (invoke ,op ,val) ,γ ,κ)
      (hconfig `(invoke ,op ,val) γ κ '()))

    ;;op invocation: handling
    (`('hconfig (invoke ,op ,val) ,γ (('cframe ,σ ('hclosure ('handler ,ret ,clauses) ,γ2)) . ,κ) ,κ2)
      (let* ([currentframe (cframe σ ('hclosure ('handler ret clauses) γ2))]
	     [resumption (append κ2 (list currentframe))])
	(match (hclause-lookup clauses op)
	  (`(,y ,resume ,body)
	    (let ([γ3 (extend-env γ2 y (value val))])
	      (config body (extend-env γ3 resume (cont-val resumption)) κ)))
	  (`()
	    (hconfig `(invoke op val) γ (push-δ κ currentframe) resumption)))))
    ))
