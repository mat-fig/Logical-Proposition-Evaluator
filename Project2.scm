;================================================================================================================
;;Helper functions
;================================================================================================================
;atom?
(define (atom? x)
  (and (not (null? x)) (not (pair? x))))

;================================================================================================================
;; Part 1
;================================================================================================================

;; Design a data type suitable for representing infix propositions, as described in my notes for Class 19.

;; Give a complete specification and development (including a proof) for a program which inputs a proposition
;; which uses and (^), or (v), not (-) and implies (=>) and which returns a logically equivalent proposition
;; using just ^ and - .  Both the input and output should use infix notation.
;================================================================================================================

; Starting with a definition:
;   prop ::= variable | (- prop) | (prop ^ prop) | (prop v prop) | (prop => prop)

; So first, we need constructors for all signs a proposition need
;; Proposition needs:  and (^), or (v), not (-) and implies (=>)

; Constructors
;Pre: make-not is called with an atom list, no pairs
;Post: the propositional logic not of the input is returned 
;DI: take an atom as an argument and return the logical not of that atom
(define (make-not p)
  (list '- p))
;Pre: make-and is called with a pair list 
;Post: the propositional logic and of the inputed pairs is returned 
;DI: take a pair as an argument and return the logical and of that them
(define (make-and p1 p2)
  (list p1 '^ p2))
;Pre: make-or is called with a pair list 
;Post: the propositional logic or of the inputed pairs is returned 
;DI: take a pair as an argument and return the logical or of that them
(define (make-or p1 p2)
  (list p1 'v p2))
;Pre: make-implies is called with a pair list
;Post: the propositional logic implies of the inputed pairs is returned 
;DI: take a pair as an argument and return the logical implies of them
(define (make-implies p1 p2)
  (list p1 '=> p2))

;Test
;(make-and 'a 'b)     ; return (a ^ b)
;(make-or 'c 'd)      ; return (c v d)
;(make-implies p1 p2) ; return ((a ^ b) => (c v d))
;(make-not p3)        ; return (- ((a ^ b) => (c v d)))


; Next, we need to build selectors to access each bot operands and the operator 
; The way infix works is we have: <first_operand><operator><second_operand>
; so lets define them now

; Selectors

;Pre: operator is called with a propositional logic list that contain a logical operator
;Post: only the logical operator is returned from the list 
;DI: Taking a propositional logic list, since '-' operator always comes first
;    the first element of the list is checked for not '-'.
;    if found, then that element is the indeed the operator.
;    But, if '-' is not first, then first element is first_operand and car of the next element will definintally be operator
;operator
(define (operator p); Example: '(a ^ b)
  (cond ((eq? '- (car p)) '-) ; (example fail this)
        (else (car (cdr p))))) ; ^ --> Its the operator!

;Pre: first_operand is called with a propositional logic list that contain a logical operator
;Post: only the first_operand is returned from the list 
;DI: Taking a propositional logic list, since '-' operator always comes first
;    the first element of the list is checked for not '-'.
;    if found, the the second element of the list is first operand.
;    But, if '-' is not first, otherwise the first element is indeed the first operand
;first-operand
(define (first_operand p); Example: '(a ^ b)
  (cond ((eq? (car p) '-) (car (cdr p))) ; (example fail this)
        (else (car p)))) ;a --> its the first_operand!

;Pre: second_operand is called with a propositional logic list that contain a logical operator that isn't a not '-'
;Post: only the second_operand is returned from the list 
;DI: Taking a propositional logic list, the third elements is indeed the second operand
;second_operand
(define (second_operand p); Example: '(a ^ b)
  (caddr p)); b --> its the second_operand!

;Test
;(operator '(a ^ b))       ; return ^
;(first_operand '(a ^ b))  ; return a
;(second_operand '(a ^ b)) ; return  b

;Next, we need to check if the current prop has not, or, and, implise operation
;So, we need Classifiers

; Classifiers

;Pre: is_not? is called with a propositional logic list p that contain a logical operator
;Post: #t is only returned if operator is equal to the logical not 
;DI: Taking a propositional logic list, check if the list is not pairs and if so, reuturn #f
;    Otherwise, check if the operator is equal to '-' and if yes, return #t 
;is_not?
(define (is_not? p)
  (cond ((atom? p) #f)
        (else (eq? (operator p) '-))))

;Pre: is_and? is called with a propositional logic list p that contain a logical operator
;Post: #t is only returned if operator is equal to the logical and 
;DI: Taking a propositional logic list, check if the list is not pairs and if so, reuturn #f
;    Otherwise, check if the operator is equal to '^' and if yes, return #t
;is_and?
(define (is_and? p)
  (cond ((atom? p) #f)
        (else (eq? (operator p) '^))))

;Pre: is_or? is called with a propositional logic p list that contain a logical operator
;Post: #t is only returned if operator is equal to the logical or 
;DI: Taking a propositional logic list, check if the list is not pairs and if so, reuturn #f
;    Otherwise, check if the operator is equal to 'v' and if yes, return #t
;is_or?
(define (is_or? p)
  (cond ((atom? p) #f)
        (else (eq? (operator p) 'v))))

;Pre: is_implies? is called with a propositional logic p list that contain a logical operator
;Post: #t is only returned if operator is equal to the logical => 
;DI: Taking a propositional logic list, check if the list is not pairs and if so, reuturn #f
;    Otherwise, check if the operator is equal to '=>' and if yes, return #t
;is_implies?
(define (is_implies? p)
  (cond ((atom? p) #f)
        (else (eq? (operator p) '=>))))

;Test
;(is_not? '(a ^ b))      ; #f
;(is_or? '(a ^ b))       ; #f
;(is_and? '(a ^ b))      ; #t
;(is_implies? '(a ^ b))  ; #f

;Now, that Constructors, Selectors, Classifiers are defined in the system.
;Its time to build write the Simplifiers which would simplify the user input
;to only using ^ and -.

; To represent the or operator in terms of - ^
; '(a v b) = (- ((-a) ^ (-b))) (By De Morgan's Law)

; Next, this is how we reprsent the implies operator
; '(a => b) = ( (- a) v b )  (By Implication)
; Now we need to change it to be built in terms of - ^ operators only
; ( (- a) v b ) = (- ((- (- a)) ^ (- b))) (By De Morgan's Law)

; Simplifiers

;DI: simplify job is to remove all the or (v) and the implies (=>) from the inputed proposition.
;    The way it works is that there is 4 possible operators any propisition could have, and we
;    know that we only need to mainly worry about the v and =>.
;
;    Case 1: The proposition list has an operator where is_not? or is_and? is #t. Then little simplification is needed.
;            basically, if is_not? is true, then using recursion, make-not and first_operand functions to keep the logical
;            proposition the same as inputed. Similar process is done when is_and? is true.
;
;    Case 2: The proposition list has an operator where is_or? or is_implies? is #t. Then simplification is needed to convert
;            them to logically equivalent proposition using make-and and make-not functions. The conversion rules followed are:
;            If is_or? is true, Ex: '(a v b) then it would be logically equivalent to the proposition (- ((-a) ^ (-b))) (By De Morgan's Law)
;            Otherwise if is_implies is true, Ex: '(a => b) then it would ne equivalent to ( (- a) v b )  (By Implication)
;            and since our simplication mechinism must not output any v or => operations for the proposition,
;            Then the proposition ( (- a) v b ) would be the same as (- ((- (- a)) ^ (- b))) (By De Morgan's Law)

;Basis case: p is not a pair list, so its an atom. Then, just return p as there is no operators or connection.

;IH: Assume function works correctly, meansing assume true for all proper components if the proposition currently under consideration
;IS: For any proposition P. There are 4 cases:
;    1. P = (a ^ b)
;       Based on the IH, there is a prop a' that is logically equivalent to a, where a' is ecpreesend using ^ and - operators.
;       Similarly, there is a prop b' that is logically equivalents to b, where b' is expressed using only ^ and - operators.
;       So, since (a ^ b) is logically equivalent to (a' ^ b') so this case does indeed uses at most ^ and - operators.
;    2. P = (- a)
;       Similar to above, there is a' that is logicially equivalent to a where a' uese only ^ and - operators. 
;    3. P = (a v b)
;       As it mentioned in the DI, (a v b) is logically equivalent to (- ((-a) ^ (-b))) (By De Morgan's Law)
;       So, similarlly, there is (- ((-a') ^ (-b'))) that is indeed logically equivalent to P using ^ and - operations.
;    4. P = (a => b)
;       Same as above, its mentioned in the DI that (a => b) is logically equivalent to ( (- a) v b )  (By Implication)
;       which is also logically equivalent to (- ((- (- a)) ^ (- b))) (By De Morgan's Law)
;       so, there is (- ((- (- a')) ^ (- b')))that is indeed logically equivalent to P using ^ and - operations.

;Termination: The program terminate after successfully modifying the logical proposition from ^,-,v,=> to the logical
;             equivalent proposition of just ^ -  

;Pre: simplify takes a proposition p which uses and (^), or (v), not (-) and implies (=>)
;Post: returns a logically equivalent proposition using just ^ and - .

;simplify
(define (simplify p)
  (cond((atom? p) p)
       ((is_not? p) (make-not (simplify (first_operand p))))
       ((is_and? p) (make-and (simplify (first_operand p))
                              (simplify (second_operand p))))
       ((is_or? p) (simplify (make-not (make-and (make-not (first_operand p))
                                                 (make-not (second_operand p))))))
       ((is_implies? p) (simplify (make-not (make-and (make-not (make-not (first_operand p)))
                                                      (make-not (second_operand p))))))))

;Test
;(simplify '(a v b))  ; return (- ((-a) ^ (-b)))
;(simplify '(a => b)) ; return (- ((- (- a)) ^ (- b)))
;(simplify '(- a))    ; return (- a)
;(simplify '(a ^ b))  ; return (a ^ b)
;================================================================================================================       
;; Part 2
;================================================================================================================

;; Give a complete specification and development (including proof) for an interpreter of infix propositions:
;; your interpreter will input a proposition and an a-list of T,F values for variables, and will return the
;; computed value of the input proposition using those values for its variables.

;================================================================================================================

;;DI: Given a variable "var" and a truth-value assocation list "a-list", we can divide and conquer down the a-list until we
;     reach a key-value that is equal to our variable. In which case, we return the value.

;;pre: lookup function takes a variable input from logical-exp and non-empty a-list hashmapping truthvalues with their respective variable
;;post: return the truth value binded to the variable
(define (lookup var a-list)
  (cond ((eq? var (caar a-list)) (cadar a-list))  
        (else (lookup var (cdr a-list)))))

;;Proof: We prove by induction on length of a-list, we will refer to it as n

;;Basis: When n = var, we return the (cadar a-list) which is the key value associated to the element var

;;IH: Assume the recursive call works for an a-list or length n-1.

;;IS: We want to show this function works for a-list of length n. When a-list is length of n we have (lookup var (cdr a-list)).
;     Here (cdr a-list) has the length of n-1. By the IH, this returns the correct value. By checking the caar of a-list,
;     we observe if the nth key of the associative list is equal to the var. If so we return the key-value.

;;Termination: Because our pre condition states we must not have an empty list or an a-list without variables in
;              our propositional s-expr, if we cdr down a-list, we will eventually reach var == (caar a-list).



;;DI: When we connect the front end with our interpreter, we no longer need to check if we have ^ OR, or => IMPLIES
;     The simplifier gave a correct logically equivalent proposition using just ^ and -. Therefore, we can simply check
;     to see if we have encountered a NOT, if so, we negate the first operand. If we encounter an AND, we and the first
;     and second operand.


;;pre: input a logical expression p using only logical expressions - or ^.
;;post: return the evaluation of these propositions
(define (eval-op p)
  (cond ((is_not? p) ((lambda (x) (list (not x))) (first_operand p)))
        ((is_and? p) ((lambda (x y) (list (and x y))) (first_operand p) (second_operand p)))))



;;DI: We know that as we traverse the list, we are bound to encounter a s-exp or an atom. We will ask if we
;     have encountered an atom, if so we return the truth value for the variable in question, if not, we will
;     have a divide and conquer strategy to divide this tree into sub-trees and reach our atom in question then,
;     appending all relevant values from the left side, with the operator, then the right side of the proposition.
;     A considerable measure is taken if we enounter a not operator, in which case we can append the not in the front,
;     then recursively call again to reach an atom. We continue this process until we reach an empty list.

;Ex: prop = ( ((- x) ^ y ) v (- z)  )

;           v
;          / \
;         ^   -
;        / \   \
;       -   y   z
;      /
;     x

;;pre: input a propositional s-expr and an a-list that binds truth values to the variables.
;;post: return a truth value evaulated based on the propsitional logic.

;;logical evaluator 
(define (interpreter prop a-list)
  (cond ((null? prop) '())
        ((atom? prop) (list (lookup prop a-list)))
        ((is_not? prop) (eval-op (append (list (operator prop)) (interpreter (first_operand prop) a-list))))                                   
        (else (eval-op (append (interpreter (first_operand prop) a-list)
                               (list (operator prop))
                               (interpreter (second_operand prop) a-list))))))


;;Proof of interpreter by structural induction

;;Basis: The most basic structure of this propostion tree is an empty tree. If we have an empty tree,
;        we return an empty list.

;;IH: Assume this recursive call works on subcomponents of the proposition tree. We assume the function evaluates
;    the variable's truth values for the given subtree.

;;IS: We must show that the function will work as expected with the current tree we have. We begin by dividing this tree
;     into two subtrees by caring and cdring, or in our case, first_operand and second_operand. The cdr of the current
;     tree is a simplier version of our current tree, therefore, based on our IH, the evaluations that the subtree is properly
;     evaluated. Also, the car of the tree is also a simplier version of the current tree. The car of the tree (first_operand),
;     can have a few possibilites:
;     Case 1: The car is an atom, in which case we return the (list (lookup (variable))) to retrieve the truth value binded for the variable. Then
;             convert to a list to later append.
;     Case 2: The car operator is '-' or not. In this case we append the (-), and make recursive calls to it, but since the car is a simpler version
;             of the original proposition tree, based off of our IH, we have properly evaluated logical expressions.
;     Case 3: The car is a list. In this case we make recursive calls to it, again, since the recursive calls produce a simplier tree, by
;             our IH, we have properly evaluated logical expressions.


;;Termination: We know that we will eventually reach the empty list for the outermost subtree because
;              we are essentially cdring down with the selector functions "first_operand" and "second_operand".
;              If the first_operand is list, we eventually cdr down to reach null. If its an atom we return the truth
;              value and return to the previous recursive step.      

(define t1 '(- ((- x) ^ (- y))))
(define t2 '( ((- x) ^ y) => (- z)) ) 
(define t3 '(- ((- x) ^ y) ^ (- z) ^ (- (x ^ y)) ^ (- z)))

(define aL '((x #t) (y #f) (z #t)))
(define a '( (y #f) (z #t)))


;================================================================================================================
;; Part 3
;================================================================================================================

;; Demonstrate your interpreter by using it in conjunction with the front-end of Part 1.

;================================================================================================================

;Pre: needs to input a logical prop and a-list with T and F values for prop variables
;Post: the truth value for the logical prop is returned
;front-end
(define (front-end proposition a-list)
  (interpreter (simplify proposition) a-list))

;Test
;(front-end '(x v y) '((x #f) (y #t)))  ; return  #t
;(front-end '(x v y) '((x #t) (y #f)))  ; return  #t
;(front-end '(x v y) '((x #t) (y #t)))  ; return  #t
;(front-end '(x v y) '((x #f) (y #f)))  ; return  #f

(display "Welcome our interpreter
This interperter takes 2 inputs.
First a logical proposition. Second a-list with #t and #f values for your prop variables")
(display "Please enter a logical Proposition:\n ^  is AND\n v  is OR\n -  is NOT\n =>  is IMPLIES\n Example: (x v y)\n> ")
(define proposition (read))
(display "Your Proposition is :" )
(display proposition)
(display "\nThe Logical Equivlent Proposition using ^ - is: " )
(display (simplify proposition))
(newline)
(display "Please enter a-list with #t and #f values for your logical proposition variables\n Example: ((x #f) (y #t))\n> ")
(define a-list (read))
(display "Your a-list is :" )
(display a-list)
(display "\nThe interpreter truth value for logical proposition and a-list values is: " )
(display (front-end proposition a-list))

