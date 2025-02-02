#lang racket/base

(require
 "verilog/counter.rkt"
 yosys/generic
 (prefix-in @ rosette/safe)
 racket/function racket/port rackunit)

(dynamically-addressable-struct person ([name 'string] [age 'number]) #:transparent)

(test-case "fields"
  (check-equal? (fields (person "Alice" 23)) '(name age)))

(test-case "get-field"
  (define p (person "Bob" 33))
  (check-equal? (get-field p 'name) "Bob")
  (check-equal? (get-field p 'age) 33))

(test-case "for/struct"
  (define p (person "Charlie" 24))
  (define p*
    (for/struct [(n f) p]
      (case n
        [(name) f]
        [(age) (add1 f)])))
  (check-equal? p* (person "Charlie" 25)))

(test-case "update-field"
  (define p (person "Dan" 11))
  (check-equal?
   (update-field p 'name "Daniel")
   (person "Daniel" 11)))

(test-case "show-diff"
  (define s0 (new-zeroed-counter_s))
  (define s1 (update-field s0 'count (@bv 3 8)))
  (define res (show-diff s0 s1))
  (define expected
    #<<EOS
{
  count: - (bv #x00 8)
         + (bv #x03 8)
}
EOS
)
  (check-equal? res expected))
