#lang racket/base

(require "concretize.rkt"
         racket/contract racket/set racket/list
         (prefix-in @ rosette/safe))

(provide
 (rename-out [only-depends-on only-depends-on/unchecked])
 (contract-out
  [only-depends-on (->
                    value-of-solvable-type?
                    (set/c @constant? #:cmp 'eq #:kind 'dont-care)
                    @solution?)]))

(define value-of-solvable-type?
  (flat-named-contract
   'value-of-solvable-type?
   (lambda (v) (@solvable? (@type-of v)))))

; is value fully determined by an assignment of concrete values
; to the given symbolics?
(define (only-depends-on value constants)
  (define value-symbolics (list->seteq (@symbolics value)))
  ; okay to depend on these:
  (define value-allowed-symbolics (set-intersect value-symbolics constants))
  ; not okay to depend on these:
  (define value-rest-symbolics (set-subtract value-symbolics constants))
  ;;; (@define-symbolic* freshh (@type-of value))
  ;;; (define res
  ;;;   (@synthesize
  ;;;     #:forall (set->list value-rest-symbolics)
  ;;;     #:guarantee
  ;;;       (@assert (@equal? value freshh))
  ;;;   ))
  ;;; (printf "synth: ~a\n" res)
  ;;; (@clear-vc!)

  (cond
    [(set-empty? value-rest-symbolics)
     ; fast path
    ;;;  (printf "rest-empty\n")
     (@unsat)]
    [(set-empty? value-allowed-symbolics)
     ; fast-ish path when we're trying to show that something
     ; is concrete (no dependence on any constants) --
     ; no exists/forall style query required
     (define concrete-value (concrete value))
     (printf "allowed-empty: ~a\t~a\n" value (@evaluate value concrete-value))
     concrete-value]
    [else
     ; need to invoke solver
     ; try to show that value doesn't depend on other symbolics
     (@define-symbolic* fresh (@type-of value))
     (define res
       (@verify
        (@assert
         (@exists (list fresh)
                  (@forall (set->list value-rest-symbolics)
                           (@equal? value fresh))))))
     res]))
