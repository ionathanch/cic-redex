#lang racket/base
#|
 | TeX-input mode symbols used:
 | λ is \lambda
 | Π is \Pi
 | Γ is \Gamma
 | · is \cdot
 | Δ is \Delta
 | Ξ is \Xi
 | Θ is \Theta
 |
 | δ is \delta
 | β is \beta
 | ζ is \zeta
 | ι is \iota
 |
 | ≡ is \equiv
 | η is \eta
 | ₁ is _1
 | ₂ is _2
 | ≼ is \preceq
 |#

(require
 redex/reduction-semantics
 (only-in racket/dict dict-ref)
 (only-in racket/function curry)
 "redex-utils.rkt"
 "snoc-env.rkt")
(module+ test
  (require redex-chk))

(provide
 (all-defined-out))

;; Syntax
(define-language cicL
  (i j k n ::= natural)
  (c D x y f r s p ::= variable-not-otherwise-mentioned)

  (U ::= (Type i) Set Prop)
  (S ::= r s p (^ S) ∞)
  (e t ::= c x d (λ (x : t) e) (@ e e) (Π (x : t) t) U (let (x = e : t) e) (case e e (e ...)) (fix f : t e))
  (d :: = (D °) (D *) (D S) D)  ;; inductive types with size annotations: bare, position, stage; D == (D ∞)
  (Γ ::= · (Γ (x : t)) (Γ (x = e : t)))
  (Δ ::= · (Δ (D : n V t Γ)))

  (v ::= ⊕ + - ○)  ;; strictly positive, positive, negative, invariant polarities
  (V ::= · (V v))   ;; vector of polarities for parameters of inductive types

  (Ξ ::= hole (Π (x : t) Ξ)) ; Telescopes, as Π contexts
  (Θ ::= hole (@ Θ e)) ; Argument lists, as application contexts

  #:binding-forms
  (λ (x : t) e #:refers-to x)
  (Π (x : t) e #:refers-to x)
  (let (x = e : t) e_body #:refers-to x)
  (fix f : t e #:refers-to f))

;; ------------------------------------------------------------------------
;; Handy meta-functions and syntax sugar

(begin ;; sugar

  ;; TODO: Proper definitions pending https://github.com/racket/redex/issues/54
  (define-extended-language cic-sugarL cicL
    (Γ-decl ::=  (x : t) (x = e : t))
    #;(C ::= (cross t))
    (me mt ::= any #;t #;C)
    (ann ::= (x : mt) mt))

  (define-metafunction cic-sugarL
    -> : ann ... mt -> mt
    [(-> mt)
     mt]
    [(-> (x : mt_0) ann ... mt)
     (Π (x : mt_0) (-> ann ... mt))]
    [(-> mt_0 ann ... mt)
     (-> (x : mt_0) ann ... mt)])

  (define-metafunction cic-sugarL
    ;; Would like this to enforce at least 1 arg, but this makes writing translation easier
    λ* : (x : mt) ... me -> me
    [(λ* me) me]
    [(λ* (x : mt) (x_r : mt_r) ... me)
     (λ (x : mt) (λ* (x_r : mt_r) ... me))])

  (define-metafunction cic-sugarL
    let* : ([x = me : mt] ...) me -> mt
    [(let* () me)
     me]
    [(let* ([x = me : mt] any_0 ...) me_body)
     (let (x = me : mt) (let* (any_0 ...) me_body))])

  (define-metafunction cic-sugarL
    @* : me me ... -> me
    [(@* me) me]
    [(@* me_0 me_1 me ...)
     (@* (@ me_0 me_1) me ...)]))

(module+ test
  (require
   (rename-in
    (submod "..")
    [@* @]
    [let* let]
    [λ* λ]))
  (provide (all-defined-out))

  (default-language cicL)
  (default-equiv (curry alpha-equivalent? cicL))

  (define-term Δ0
    (· (False : 0 · Prop ·)))

  (define-term Δ01
    (Δ0 (Unit : 0 · Prop (· (tt : Unit)))))

  (define-term Δb
    (Δ01 (Bool : 0 · Set ((· (true : Bool)) (false : Bool)))))

  (define-term Δnb
    (Δb (Nat : 0 · Set ((· (z : Nat)) (s : (Π (x : Nat) Nat))))))

  ;; Tests parameters
  (define-term Δlist
    (Δnb (List : 1 (· ⊕) (Π (A : Set) Set)
                ((· (nil : (Π (A : Set) (@ List A))))
                 (cons : (-> (A : Set) (a : A) (ls : (@ List A)) (@ List A)))))))

  ;; Check that all constructors have explicit parameter declarations; implicit is surface sugar
  (define-term Δbadlist
    (Δnb (List : 1 (· ⊕) (Π (A : Set) Set)
                ((· (nil : (@ List A)))
                 (cons : (-> (a : A) (ls : (@ List A)) (@ List A)))))))

  (define-term subn
    (fix f : (Π (x : Nat) Nat)
         (λ (x : Nat)
           (case x (λ (x : Nat) Nat) (z (λ (x : Nat) (@ f x)))))))

  #;(define-term subn
    (fix f : (Π (x : (Nat *)) (Nat °))
         (λ (x : (Nat °))
           (case x (λ (x : (Nat (^ s))) Nat) (z (λ (x : (Nat s)) (@ f x)))))))

  (define-term plus
    (fix add : (Π (n : Nat) (Π (m : Nat) Nat))
      (λ (n : Nat)
        (λ (m : Nat)
          (case n (λ (x : Nat) Nat)
            (m
             (λ (x : Nat)
               (@ s (@ (@ add x) m)))))))))

  #;(define-term plus
    (fix add : (Π (n : (Nat *)) (Π (m : (Nat °)) (Nat °)))
      (λ (n : (Nat °))
        (λ (m : (Nat °))
          (case n (λ (x : (Nat (^ s))) Nat)
            (m
             (λ (x : (Nat s))
               (@ s (@ (@ add x) m)))))))))

  ;; ill-typed but well-formed
  (define-term subn-bad1
    (fix f : (Π (x : (Nat *)) (Nat °))
         (λ (x : (Nat °))
           (case x (λ (x : (Nat (^ s))) Nat) (z (λ (x : (Nat s)) (@ f z)))))))

  (define-term subn-bad2
    (fix f : (Π (x : (Nat *)) (Nat °))
         (λ (A : Set)
           (λ (x : (Nat °))
             (case x (λ (x : (Nat (^ s))) Nat) (z (λ (x : (Nat s)) (@ f x))))))))

  (define-term Ω
    (fix f : (Π (x : (Nat *)) (Nat °))
         (λ (x : (Nat °))
           (@ f x))))

  (redex-chk
   #:lang cicL
   #:m Δ Δnb
   #:m Δ Δlist
   #:m Δ Δbadlist
   #:m (cross e) hole
   #:m (cross e) (@ (λ (x : t) hole) z)
   #:m U Prop
   #:m U (Type 0)
   #:m U Set
   #:f #:m U Type
   #:f #:m e (fix x : Type x)
   #:m e (fix x : Set x)
   #:m (in-hole hole (Π (x : D) U)) (Π (x : Nat) Set)
   #:m (in-hole Ξ_D (Π (x : D) U)) (Π (x : Nat) Set)
   #:m e subn
   #:m e plus
   #:m e subn-bad1
   #:m e subn-bad2
   #:m e Ω
   #:m (in-hole Θ Nat) (@ Nat)
   #:m (in-hole Ξ (in-hole Θ Nat)) (Π (x : Nat) (@ Nat))
   #:m (in-hole hole (Π (x : (in-hole Θ D)) U)) (Π (x : (@ Nat)) Set)
   #:m (in-hole Ξ_D (Π (x : (in-hole Θ D)) U)) (Π (x : (@ Nat)) Set)))

;; ------------------------------------------------------------------------
;; Universes

(begin ;; universes

  ;; What is the upper bound on two universes
  (define-judgment-form cicL
    #:mode (<=U I I)
    #:contract (<=U U U)

    [-------------
     (<=U Prop U)]

    [--------------
     (<=U Set Set)]

    [-------------------
     (<=U Set (Type i))]

    [(side-condition ,(<= (term i) (term j)))
     ------------------------
     (<=U (Type i) (Type j))])

  (define-judgment-form cicL
    #:mode (max-U I I O)
    #:contract (max-U U U U)

    [(<=U U_1 U_2)
     --------------------
     (max-U U_1 U_2 U_2)]

    [(<=U U_2 U_1)
     --------------------
     (max-U U_1 U_2 U_1)]))

(module+ test
  (redex-judgment-holds-chk
   <=U
   [Prop Set]
   [Prop Prop]
   [Set Set]
   [Prop (Type 5)]
   [Set (Type 5)]
   [#:f (Type 5) Set]
   [#:f (Type 5) Prop]
   [#:f Set Prop]
   [#:f (Type 5) (Type 1)])

  (redex-judgment-holds-chk
   max-U
   [Prop Set Set]
   [Prop Prop Prop]
   [Set Set Set]
   [Prop (Type 5) (Type 5)]
   [Set (Type 5) (Type 5)]
   [(Type 5) Set (Type 5)]
   [(Type 5) Prop (Type 5)]
   [Set Prop Set]
   [(Type 5) (Type 1) (Type 5)]))

;; ------------------------------------------------------------------------
;; Stages

(begin ;; stages

  ;; substages
  (define-judgment-form cicL
    #:mode (<=S I I)
    #:contract (<=S S S)

    [----------
     (<=S S S)]

    [--------------
     (<=S S (^ S))]

    [----------
     (<=S S ∞)]))

(module+ test
  (redex-judgment-holds-chk
   <=S
   [s s]
   [s (^ s)]
   [s ∞]))

;; ------------------------------------------------------------------------
;; Dynamic Semantics.

(begin ;; dynamics

  ;; small step reductions
  (define (cicL--> Δ Γ)
    (term-let ([Γ Γ] [Δ Δ])
      (reduction-relation
       cicL
       (--> x e
            (where (x = e : t) (snoc-env-ref Γ x))
            "δ")
       (--> (@ (λ (x : t) e_0) e_1)
            (substitute e_0 x e_1)
            "β")
       (--> (let (x = e_0 : t) e_1)
            (substitute e_1 x e_0)
            "ζ")
       (--> (case (in-hole Θ c_i) _ (e_0 ... e_n))
            (in-hole Θ_i e_i)
            (where #t (Δ-in-constructor-dom Δ c_i))
            (where/hidden e_i (select-method Δ c_i e_0 ... e_n))
            (where Θ_i (take-indicies Δ c_i Θ))
            "ι1")
       (--> (@ (name e_f (fix f : t_f (λ (x : t) e))) (name e_a (in-hole Θ c)))
            (substitute (substitute e f e_f) x e_a)
            (where #t (Δ-in-constructor-dom Δ c))
            "ι2"))))

  ;; Select the method in e ... that corresponds to the constructor c
  (define-metafunction cicL
    select-method : Δ c e ... -> e
    [(select-method Δ c e ..._0)
     e_mi
     (where D (Δ-key-by-constructor Δ c))
     ;; Methods must match number of constructors
     (where (c_r ..._0) (Δ-ref-constructors Δ D))
     (where e_mi ,(dict-ref (term ((c_r . e) ...)) (term c)))])

  ;; Reduce anywhere
  (define (cicL-->* Δ Γ)
    (compatible-closure (cicL--> Δ Γ) cicL e))

  ;; Reduce e to a normal form
  (define-metafunction cicL
    reduce : Δ Γ e -> e
    [(reduce Δ Γ e)
     ,(car (apply-reduction-relation* (cicL-->* (term Δ) (term Γ)) (term e) #:cache-all? #t))])

  ;; A judgment version, for easy use in the type system
  (define-judgment-form cicL
    #:mode (normalize I I I O)
    #:contract (normalize Δ Γ e e)

    [(where e_0 (reduce Δ Γ e))
     ----------------------
     (normalize Δ Γ e e_0)]))

(module+ test
  (redex-chk
   #:lang cicL
   (reduce Δnb · Nat) Nat
   (reduce · · (@ (λ (x : (Type 0)) x) z)) z
   (reduce · · f) f
   (reduce · · (in-hole (@ hole z) (λ (x : (Nat °)) Nat))) Nat
   (reduce Δnb · (case z (λ (x : (Nat (^ s))) Nat) (z (λ (x : (Nat s)) x)))) z
   (reduce Δlist · (case (@ nil Nat) (λ (ls : (@ (List (^ s)) Nat)) Bool) (true false))) true
   (reduce Δnb (· (x : Nat)) (@ subn x)) (@ subn x)
   (reduce Δnb · (@ subn z)) z
   (reduce Δnb · (@ subn (@ s z))) z
   (reduce Δnb · (@ (@ plus z) z)) z
   (reduce Δnb · (@ (@ plus (@ s z)) z)) (@ s z)
   (reduce Δnb · (@ (@ plus z) (@ s z))) (@ s z)
   (reduce Δnb · (@ (@ plus (@ s z)) (@ s z))) (@ s (@ s z))))

;; ------------------------------------------------------------------------
;; Equivalence

(define-judgment-form cicL
  #:mode (convert I I I I)
  #:contract (convert Δ Γ e_1 e_2)

  [(normalize Δ Γ e_0 e_0p)
   (normalize Δ Γ e_1 e_1p)
   ;; NB: workaround issue #99 https://github.com/racket/redex/issues/99
   (where (e e) (e_0p e_1p))
   ----------------- "≡"
   (convert Δ Γ e_0 e_1)]

  [(normalize Δ Γ e_0 (λ (x : t) e))
   (normalize Δ Γ e_1 e_2)
   (convert Δ (Γ (x : t)) e (@ e_2 x))
   ----------------- "≡-η₁"
   (convert Δ Γ e_0 e_1)]

  [(normalize Δ Γ e_1 (λ (x : t) e))
   (normalize Δ Γ e_0 e_2)
   (convert Δ (Γ (x : t)) (@ e_2 x) e)
   ----------------- "≡-η₂"
   (convert Δ Γ e_0 e_1)])

(module+ test
  (define ((cicL-equiv Δ Γ) x y)
    (judgment-holds (convert ,Δ ,Γ ,x ,y)))

  (parameterize ([default-equiv (cicL-equiv (term Δnb) (term ·))])
    (redex-chk
     #:lang cicL
     #:eq (λ (x : Set) (@ f x)) (reduce · (· (f : (Π (x : Set) Set))) f)
     #:eq (λ (x : (Nat °)) (@ s x)) (reduce Δnb · s)
     #:eq z (@ subn z)
     #:eq z (@ subn (@ s z))
     #:eq (Π (y : Set) Set) (Π (p : Set) Set))))

;; ------------------------------------------------------------------------
;; Subtyping

;; Is e_1 a subtype of e_2
;; NB: Not quite as specified; ≼-U axioms instead of deriving them
(define-judgment-form cicL
  #:mode (subtype I I I I)
  #:contract (subtype Δ Γ e_1 e_2)

  [(convert Δ Γ e_0 e_1)
   ---------------------- "≼-≡"
   (subtype Δ Γ e_0 e_1)]

  [(<=U U_0 U_1)
   ---------------------- "≼-U"
   (subtype Δ Γ U_0 U_1)]

  [(convert Δ Γ t_0 t_1)
   (subtype Δ (Γ (x_0 : t_0)) e_0 (substitute e_1 x_1 x_0))
   ------------------------------------------------------ "≼-Π"
   (subtype Δ Γ (Π (x_0 : t_0) e_0) (Π (x_1 : t_1) e_1))]

  ;; Fully-applied inductive type ((D S) ps as)
  ;; is a subtype of ((D S') ps' as')
  ;; if S ⊑ S', ps ≼ ps' wrt V, and as ≡ as'
  ;; where V is the vector of polarities for D
  [(<=S S_0 S_1)
   (where Θ_0p (take-parameters Δ D Θ_0))
   (where Θ_1p (take-parameters Δ D Θ_1))
   (where (e_0 ...) (Θ-flatten (take-indicies Δ D Θ_0)))
   (where (e_1 ...) (Θ-flatten (take-indicies Δ D Θ_1)))
   (where V (Δ-ref-polarities Δ D))
   (subtype-vector Δ Γ V Θ_0p Θ_1p)
   (convert Δ Γ e_0 e_1) ...
   ---------------------------------------------------------- "≼-D"
   (subtype Δ Γ (in-hole Θ_0 (D S_0)) (in-hole Θ_1 (D S_1)))])

(define-judgment-form cicL
  #:mode (subtype-vector I I I I I)
  #:contract (subtype-vector Δ Γ V Θ_0 Θ_1)

  [(convert Δ Γ e_0 e_1)
   (subtype-vector Δ Γ V Θ_0 Θ_1)
   --------------------------------------------------- "vst-inv"
   (subtype-vector Δ Γ (V ○) (@ Θ_0 e_0) (@ Θ_1 e_1))]

  [(subtype Δ Γ e_0 e_1)
   (subtype-vector Δ Γ V Θ_0 Θ_1)
   --------------------------------------------------- "vst-strict-pos"
   (subtype-vector Δ Γ (V ⊕) (@ Θ_0 e_0) (@ Θ_1 e_1))]

  [(subtype Δ Γ e_0 e_1)
   (subtype-vector Δ Γ V Θ_0 Θ_1)
   --------------------------------------------------- "vst-pos"
   (subtype-vector Δ Γ (V +) (@ Θ_0 e_0) (@ Θ_1 e_1))]

  [(subtype Δ Γ e_1 e_0)
   (subtype-vector Δ Γ V Θ_0 Θ_1)
   --------------------------------------------------- "vst-neg"
   (subtype-vector Δ Γ (V -) (@ Θ_0 e_0) (@ Θ_1 e_1))]

  ;; Θ should be holes in this rule
  ;; not sure why the rule has them as vectors in Fig. 2.1
  [(where (e_0 ...) (Θ-flatten Θ_0))
   (where (e_1 ...) (Θ-flatten Θ_1))
   (convert Δ Γ e_0 e_1) ...
   ------------------------------- "vst-conv"
   (subtype-vector Δ Γ · Θ_0 Θ_1)])

(module+ test
  (redex-judgment-holds-chk
   (subtype Δlist ·)
   [Prop Prop]
   [Prop Set]
   [Prop (Type 1)]
   [Set (Type 1)]
   [#:f Set Prop]
   [Set (Type 5)]
   [(Type 1) (Type 5)]
   [#:f (Type 5) (Type 1)]
   [(Π (x : Prop) Prop) (Π (x : Prop) Set)]
   [#:f (Π (x : Prop) Prop) (Π (x : Set) Set)]
   [#:f (Π (x : Set) Prop) (Π (x : Prop) Set)]
   [(Π (x : Set) Prop) (Π (x : Set) Set)]
   [(@ (λ (x : (Type 1)) Set) Set) Set]
   [(@ (List S) Nat) (@ (List (^ S)) Nat)]))

(module+ test
  (redex-judgment-holds-chk
   (subtype-vector · ·)
   [· hole hole]
   [(· ⊕) (@ hole Prop) (@ hole Set)]
   [(· +) (@ hole Prop) (@ hole Set)]
   [(· -) (@ hole Set) (@ hole Prop)]
   [(· ○) (@ hole Prop) (@ hole Prop)]
   [((· -) +) (@ (@ hole Set) Prop) (@ (@ hole Prop Set))]))

;; ------------------------------------------------------------------------
;; Typing

(begin ;; well-formed environment

  ;; Make sure length of polarities is the same as number of parameters
  (define-judgment-form cicL
    #:mode (valid-polarities I I)
    #:contract (valid-polarities n V)

    [-----------------------
     (valid-polarities 0 ·)]

    [(valid-polarities ,(sub1 (term n)) V)
     ---------------------------
     (valid-polarities n (V _))])

  (define-judgment-form cicL
    #:mode (valid-parameters I I I I)
    #:contract (valid-parameters Δ n t t)

    [-------------------------------
     (valid-parameters Δ 0 t_0 t_1)]

    [(valid-parameters Δ ,(sub1 (term n)) t_0 t_1)
     -------------------------------------------------------
     (valid-parameters Δ n (Π (x : t) t_0) (Π (y : t) t_1))])

  (define-judgment-form cicL
    #:mode (constructor-type I I I)
    #:contract (constructor-type Δ D t)

    [-----------------------------------------
     (constructor-type Δ D (in-hole Θ (D ∞)))]

    [-----------------------------------------
     (constructor-type Δ D (in-hole Θ D))]

    [(side-condition (free-in x t_2))
     (side-condition (not-free-in D t_1))
     (constructor-type Δ D t_2)
     ----------------------------------------- ;; Πx: T1. T2
     (constructor-type Δ D (Π (x : t_1) t_2))]

    [(side-condition (not-free-in x t_2))
     (strict-positivity Δ D t_1)
     (constructor-type Δ D t_2)
     ----------------------------------------- ;; T1 -> T2
     (constructor-type Δ D (Π (x : t_1) t_2))])

  (define-judgment-form cicL
    #:mode (valid-constructor I I)
    #:contract (valid-constructor Δ c)

    [;; variables
     (where (D : n V (name t_D (in-hole Ξ_d t)) _) (Δ-ref-by-constructor Δ c))
     (where (name t_c (in-hole Ξ_c (in-hole Θ _))) (Δ-ref-constructor-type Δ c))
     (where (name params ((x_p : t_p) ...)) (Ξ-take Ξ_c n))
     (where Ξ_i (Ξ-drop Ξ_c n))
     (where (x_ni ...) (noninvariant-variables V params))
     (where (x_sp ...) (strictly-positive-variables V params))
     ;; clauses
     (valid-parameters Δ n t_c t_D) ;; constructor has same parameters as inductive type
     (type-infer Δ · t_c (Type k)) ;; I2 (maybe redundant, given I4?)
     (constructor-type Δ D t_c) ;; I4
     (side-condition (full-types-only t_c)) ;; I5
     ;; I6
     (side-condition ((not-free-in x_ni Θ) ...)) ;; I7
     (strict-positivity Δ x_sp (in-hole Ξ_i Set)) ... ;; I9; use Set to plug the hole
     ------------------------
     (valid-constructor Δ c)])

  ;; Holds when the type t is a valid type for a constructor of D
  (define-judgment-form cicL
    #:mode (valid-constructors I I)
    #:contract (valid-constructors (Δ (D : n V t Γ)) Γ)

    [------------------------- "VC-Empty"
     (valid-constructors Δ ·)]

    [;; constructor's type must return the inductive type D
     (where (in-hole Ξ (in-hole Θ D)) t)
     ;; First n arguments (parameters) of the constructor must match those of the inductive
     (valid-parameters Δ n t t_D)
     (strict-positivity-cond Δ_0 (· (D : t_D)) D t)
     (type-infer Δ (· (D : t_D)) t U)
     (valid-constructors Δ_0 Γ_c)
     -----------------------------------------------------------------"VC-C"
     (valid-constructors (name Δ_0 (Δ (D : n _ t_D _))) (Γ_c (c : t)))])

  ;; Under global declarations Δ, is the term environment well-formed?
  (define-judgment-form cicL
    #:mode (wf I I)
    #:contract (wf Δ Γ)

    [--------- "W-Empty"
     (wf · ·)]

    [(wf Δ Γ)
     (type-infer Δ Γ t U)
     ------------------- "W-Local-Assum"
     (wf Δ (Γ (x : t)))]

    [(wf Δ Γ)
     (type-check Δ Γ e t)
     (type-infer Δ Γ t U)
     ----------------------- "W-Local-Def"
     (wf Δ (Γ (x = e : t)))]

    ;; NB: Not quite as specified:
    ;; * valid-constructors loops over constructors, rather than precomputing environments and using ... notation
    ;;   Primarily this is because ... notation makes checking the result type of each constructor
    ;;   awkward, but also ... notation makes random testing harder.
    ;; * check t_D directly rather than splitting parameter telescope manually.
    ;; * Γ must be empty, to guide search
    [(wf Δ ·)
     (where #f (Δ-in-dom Δ D))
     (where (c_i ...) (Δ-ref-constructors Δ_0 D))
     (where (c_!_0 ...) (c_i ...)) ; all constructors unique
     (type-infer Δ · t_D U_D)
     (valid-constructors Δ_0 Γ_c)
     (valid-polarities n V)
     ---------------------------------------------------------- "W-Ind"
     (wf (name Δ_0 (Δ (D : n V (name t_D (in-hole Ξ U)) Γ_c))) ·)]))

(module+ test
  (redex-judgment-holds-chk
   (valid-constructors Δ01)
   [(· (tt : Unit))])

  (redex-relation-chk
   wf
   [· ·]
   [Δ0 ·]
   [Δ01 ·]
   [Δb ·]
   [Δnb ·]
   [Δnb (· (x : Nat))]
   [Δlist ·]
   [#:f Δbadlist ·]
   [Δlist (· (x = (λ (x : Nat) (λ (y : Nat) y)) : (Π (x : Nat) (Π (y : Nat) Nat))))]
   [Δlist ((· (x = (λ (x : Nat) (λ (y : Nat) y)) : (Π (x : Nat) (Π (y : Nat) Nat))))
           (y = (λ (x : Nat) (λ (y : Nat) y)) : (Π (x : Nat) (Π (y : Nat) Nat))))]
   #;[Δlist (· (x = (λ (x : (Nat °)) (λ (y : (Nat °)) y)) : (Π (x : Nat) (Π (y : Nat) Nat))))]
   #;[Δlist ((· (x = (λ (x : (Nat °)) (λ (y : (Nat °)) y)) : (Π (x : Nat) (Π (y : Nat) Nat))))
           (y = (λ (x : (Nat °)) (λ (y : (Nat °)) y)) : (Π (x : Nat) (Π (y : Nat) Nat))))]
   [Δlist (· (x = subn : (Π (y : Nat) Nat)))]
   [Δnb (· (x = subn : (Π (y : Nat) Nat)))]
   ; This passes, but is very slow without a large cache.
   #;[Δnb ((· (x = subn : (Π (y : Nat) Nat)))
           (z = subn : (Π (y : Nat) Nat)))]))

(begin ;; typing

  ;; Under global declarations Δ and term environment Γ, can we infer a type t for term e?
  (define-judgment-form cicL
    #:mode (type-infer I I I O)
    #:contract (type-infer Δ Γ e t)

    [(wf Δ Γ)
     ------------------------------- "Ax-Prop"
     (type-infer Δ Γ Prop (Type 1))]

    [(wf Δ Γ)
     ------------------------------ "Ax-Set"
     (type-infer Δ Γ Set (Type 1))]

    [(wf Δ Γ) (where j ,(add1 (term i)))
     ----------------------------------- "Ax-Type"
     (type-infer Δ Γ (Type i) (Type j))]

    [(Γ-in Γ x t) (wf Δ Γ)
     --------------------- "Var"
     (type-infer Δ Γ x t)]

    [(type-infer Δ Γ t_0 U)
     (type-check Δ (Γ (x : t_0)) t Prop)
     -------------------------------------- "Prod-Prop"
     (type-infer Δ Γ (Π (x : t_0) t) Prop)]

    [(type-infer Δ Γ t_0 U)
     (in U (Set Prop))
     (type-check Δ (Γ (x : t_0)) t Set)
     ------------------------------------- "Prod-Set"
     (type-infer Δ Γ (Π (x : t_0) t) Set)]

    [(type-infer Δ Γ t_0 U_1)
     (type-infer Δ (Γ (x : t_0)) t U_2)
     ;; NB: Not quite as specified, to make algorithmic.
     (max-U U_1 U_2 U_3)
     ------------------------------------- "Prod-Type"
     (type-infer Δ Γ (Π (x : t_0) t) U_3)]

    [(type-infer Δ (Γ (x : t_0)) e t)
     (type-infer Δ Γ (Π (x : t_0) t) U)
     ------------------------------------------------- "Lam"
     (type-infer Δ Γ (λ (x : t_0) e) (Π (x : t_0) t))]

    [(type-infer Δ Γ e_0 (Π (x : t_1) t))
     (type-check Δ Γ e_1 t_1)
     -------------------------------------------------- "App"
     (type-infer Δ Γ (@ e_0 e_1) (substitute t x e_1))]

    [(type-check Δ Γ e t)
     (type-infer Δ (Γ (x = e : t)) e_body t_body)
     ------------------------------------------------------------------ "Let"
     (type-infer Δ Γ (let (x = e : t) e_body) (substitute t_body x e))]

    [(Δ-type-in Δ D t) (wf Δ Γ)
     --------------------- "Ind"
     (type-infer Δ Γ D t)]

    [(Δ-type-in Δ D t) (wf Δ Γ)
     --------------------- "Ind-sized"
     (type-infer Δ Γ (D S) t)]

    [(Δ-constr-in Δ c t) (wf Δ Γ)
     --------------------- "Constr"
     (type-infer Δ Γ c t)]

    [(type-infer Δ Γ e (name t_I (in-hole Θ D)))
     (where Θ_p (take-parameters Δ D Θ))  ;; Extend Γ with parameters determined from e_Di ...
     (where Θ_i (take-indicies Δ D Θ))
     (check-motive Δ Γ t_I D Θ_p e_motive) ;; Check the motive matches the inductive type
     (where t (@ (in-hole Θ_i e_motive) e)) (type-infer Δ Γ t U)
     (check-methods Δ Γ D t Θ_p (e_m ...)) ;; Check the methods match their constructors, and return type from motive
     ------------------------------------------------- "match"
     (type-infer Δ Γ (case e e_motive (e_m ..._1)) t)]

    [(terminates Δ e_fix)
     (type-infer Δ Γ t U)
     (type-check Δ (Γ (f : t)) e t)
     ---------------------------------------------- "Fix"
     (type-infer Δ Γ (name e_fix (fix f : t e)) t)])

  ;; Under global declarations Δ and term environment Γ, does e have a type that is convertible to t?
  (define-judgment-form cicL
    #:mode (type-check I I I I)
    #:contract (type-check Δ Γ e t)

    [(type-infer Δ Γ e t_1) (type-infer Δ Γ t U) (subtype Δ Γ t_1 t)
     --------------------- "Conv"
     (type-check Δ Γ e t)]))

(module+ test
  (redex-judgment-holds-chk
   (type-infer · ·)
   [(Type 0) (Type 1)]
   [(Π (a : Prop) Prop) U])

  (redex-relation-chk
   (type-check · ·)
   [(Type 0) (Type 1)]
   [#:f (Π (x : (Type 0)) (Type 0)) (Type 0)]
   [(Π (x : (Type 0)) (Type 0)) (Type 1)]
   [#:f (Π (x : (Type 0)) x) (Type 0)]
   [#:f Prop (Type 0)]
   [Set (Type 1)]
   [Prop (Type 1)]
   [Prop (Type 2)]
   [(Π (x : Set) Set) (Type 1)]
   [(Π (x : Prop) x) Prop]
   [(Π (x : Prop) Prop) (Type 1)]
   [(λ (x : Set) x) (Π (x : Set) Set)]
   [(λ (x : Set) x) (-> Set Set)])

  (redex-judgment-holds-chk
   (type-infer Δlist ·)
   [(λ (x : Nat) Nat) t]
   [(λ (x : Nat) Nat) t]
   #;[(λ (x : (Nat °)) Nat) t]
   [(case z (λ (x : Nat) Nat) (z (λ (x : Nat) x))) t]
   #;[(case z (λ (x : (Nat (^ s))) Nat) (z (λ (x : (Nat s)) x))) t]
   [#:f nil (@ List A)]
   [nil (Π (x : Set) (@ List x))]
   [(@ nil Nat) t]
   [(@ List Nat) Set]
   [List (Π (x_A : Set) Set)]
   [cons (Π (x_A : Set) (Π (x_a : x_A) (Π (x_r : (@ List x_A)) (@ List x_A))))]
   [(@ cons Nat z (@ nil Nat)) t]
   [subn t]
   [plus t]
   [#:f subn-bad1 t]
   [#:f subn-bad2 t]
   [#:f Ω t])

  (redex-relation-chk
   type-check
   [· (· (Nat : (Type 0))) (Π (n : Nat) Nat) (Type 1)]
   [· (· (Nat : Set)) (Π (n : Nat) Nat) (Type 1)]
   [Δnb (· (x : Nat)) Nat Set]
   [Δnb (· (Nat : Set)) (λ (n : Nat) n) (Π (n : Nat) Nat)]
   #;[(case z (λ (x : (Nat (^ s))) Nat) (z (λ (x : (Nat s)) x))) t]
   [Δnb ((· (f : (-> Nat Nat))) (x : Nat))
        (case x (λ (x : Nat) Nat)
              (z
               (λ (x : Nat) (@ f x))))
        Nat]
    #;[Δnb ((· (f : (-> Nat Nat))) (x : Nat))
        (case x (λ (x : (Nat (^ s))) Nat)
              (z
               (λ (x : (Nat s)) (@ f x))))
        Nat]
   [Δnb (· (f : (-> Nat Nat)))
    (λ (x : Nat)
      (case x (λ (x : Nat) Nat)
            (z
             (λ (x : Nat) (@ f x)))))
    (Π (y : Nat) Nat)]
    #;[Δnb (· (f : (-> Nat Nat)))
    (λ (x : (Nat °))
      (case x (λ (x : (Nat (^ s))) Nat)
            (z
             (λ (x : (Nat s)) (@ f x)))))
    (Π (y : Nat) Nat)])

  (redex-relation-chk
   (type-check Δlist ·)
   [Nat Set]
   [z Nat]
   [(@ s z) Nat]
   [(Π (x : Nat) Set) (Type 1)]
   [(λ (x : Nat) Nat) (Π (x : Nat) Set)]
   #;[(λ (x : (Nat °)) Nat) (Π (x : Nat) Set)]
   [(λ (x : Nat) x) (Π (x : Nat) Nat)]
   #;[(λ (x : (Nat °)) x) (Π (x : Nat) Nat)]
   [(case z (λ (x : Nat) Nat) (z (λ (x : Nat) x))) Nat]
   #;[(case z (λ (x : (Nat (^ s))) Nat) (z (λ (x : (Nat s)) x))) Nat]
   [(case true (λ (x : Bool) Nat) (z (@ s z))) Nat]
   #;[(case true (λ (x : (Bool (^ s))) Nat) (z (@ s z))) Nat]
   [(fix f : (-> Nat Nat)
         (λ (x : Nat)
           (case x (λ (x : Nat) Nat)
                 (z
                  (λ (x : Nat) (@ s x))))))
    (Π (x : Nat) Nat)]
   #;[(fix f : (-> (Nat *) Nat)
         (λ (x : (Nat °))
           (case x (λ (x : (Nat (^ s))) Nat)
                 (z
                  (λ (x : (Nat s)) (@ s x))))))
    (Π (x : Nat) Nat)]
   [(fix f : (-> Nat Nat)
         (λ (x : Nat)
           (case x (λ (x : Nat) Nat)
                 (z
                  (λ (x : Nat) (@ f x))))))
    (Π (x : Nat) Nat)]
   #;[(fix f : (-> (Nat *) Nat)
         (λ (x : (Nat °))
           (case x (λ (x : (Nat (^ s))) Nat)
                 (z
                  (λ (x : (Nat s)) (@ f x))))))
    (Π (x : Nat) Nat)]
   [#:f (fix f : (-> Nat Nat)
             (λ (x : Nat)
               (case x (λ (x : Nat) Nat)
                     ((@ f x)
                      (λ (y : Nat) (@ f x))))))
    (Π (x : Nat) Nat)]
   #;[#:f (fix f : (-> Nat Nat)
             (λ (x : (Nat °))
               (case x (λ (x : (Nat (^ s))) Nat)
                     ((@ f x)
                      (λ (y : (Nat s)) (@ f x))))))
    (Π (x : Nat) Nat)]
   [(let ([n = z : Nat]) z) Nat]
   [(let ([n = z : Nat]) n) Nat]
   [(let ([Nat^ = Nat : Set] [n = z : Nat^]) n) Nat]
   [(@ cons Nat z (@ nil Nat)) (@ List Nat)]
   [(case (@ cons Nat z (@ nil Nat)) (λ (ls : (@ List Nat)) Bool)
          (true (λ (n : Nat) (ls : (@ List Nat)) false))) Bool]
   #;[(case (@ cons Nat z (@ nil Nat)) (λ (ls : (@ (List (^ s)) Nat)) Bool)
          (true (λ (n : Nat) (ls : (@ (List s) Nat)) false))) Bool]))

;; ------------------------------------------------------------------------
;; Typing aux

(begin ;; positivity/negativity of stage variables

  (define-judgment-form cicL
    #:mode (pos-stage I I I)
    #:contract (pos-stage Δ s e)

    [(side-condition (not-free-in s e))
     ------------------
     (pos-stage Δ s e)]

    [(neg-stage Δ s t_0) (pos-stage Δ s t_1)
     ----------------------------------
     (pos-stage Δ s (Π (x : t_0) t_1))]

    [(where Θ_p (take-parameters Δ D Θ))
     (where Θ_a (take-indicies   Δ D Θ))
     (where V (Δ-ref-polarities Δ D))
     (pos-stage-vector Δ V s Θ_p)
     (side-condition (not-free-in s Θ_a))
     ----------------------------------
     (pos-stage Δ s (in-hole Θ (D S)))])

  (define-judgment-form cicL
    #:mode (neg-stage I I I)
    #:contract (neg-stage Δ s e)

    [(side-condition (not-free-in s e))
     ------------------
     (neg-stage Δ s e)]

    [(pos-stage Δ s t_0) (neg-stage Δ s t_1)
     ----------------------------------
     (neg-stage Δ s (Π (x : t_0) t_1))]

    [(side-condition ,(not (eq? (term (bare S)) (term s))))
     (where Θ_p (take-parameters Δ D Θ))
     (where Θ_a (take-indicies   Δ D Θ))
     (where V (Δ-ref-polarities Δ D))
     (neg-stage-vector Δ V s Θ_p)
     (side-condition (not-free-in s Θ_a))
     ----------------------------------
     (neg-stage Δ s (in-hole Θ (D S)))])

  (define-judgment-form cicL
    #:mode (pos-stage-vector I I I I)
    #:contract (pos-stage-vector Δ V s Θ)

    [------------------------------
     (pos-stage-vector Δ · s hole)]

    [(pos-stage Δ s e)
     (pos-stage-vector Δ V s Θ)
     ------------------------------------
     (pos-stage-vector Δ (V ⊕) s (@ Θ e))]

    [(pos-stage Δ s e)
     (pos-stage-vector Δ V s Θ)
     ------------------------------------
     (pos-stage-vector Δ (V +) s (@ Θ e))]

    [(neg-stage Δ s e)
     (pos-stage-vector Δ V s Θ)
     ------------------------------------
     (pos-stage-vector Δ (V -) s (@ Θ e))]

    [(side-condition (not-free-in s e))
     (pos-stage-vector Δ V s Θ)
     ------------------------------------
     (pos-stage-vector Δ (V ○) s (@ Θ e))])

  (define-judgment-form cicL
    #:mode (neg-stage-vector I I I I)
    #:contract (neg-stage-vector Δ V s Θ)

    [------------------------------
     (neg-stage-vector Δ · s hole)]

    [(neg-stage Δ s e)
     (neg-stage-vector Δ V s Θ)
     ------------------------------------
     (neg-stage-vector Δ (V ⊕) s (@ Θ e))]

    [(neg-stage Δ s e)
     (neg-stage-vector Δ V s Θ)
     ------------------------------------
     (neg-stage-vector Δ (V +) s (@ Θ e))]

    [(pos-stage Δ s e)
     (neg-stage-vector Δ V s Θ)
     ------------------------------------
     (neg-stage-vector Δ (V -) s (@ Θ e))]

    [(side-condition (not-free-in s e))
     (neg-stage-vector Δ V s Θ)
     ------------------------------------
     (neg-stage-vector Δ (V ○) s (@ Θ e))]))

(module+ test
  (redex-judgment-holds-chk
   (pos-stage Δlist)
   [s Prop]
   [s (Π (x : Prop) Set)]
   [s (@ (List s) (Nat s))]
   [s (Π (n : Nat) (@ (List s) Nat))]))

(module+ test
  (redex-judgment-holds-chk
   (neg-stage Δlist)
   [s Prop]
   [s (Π (x : Prop) Set)]
   [s (@ (List r) (Nat r))]
   [s (Π (l : (@ (List s) Nat)) (Nat r))]))

(module+ test
  (redex-judgment-holds-chk
   (pos-stage-vector Δlist)
   [· s hole]
   [(· ⊕) s (@ hole (@ (List s) Nat))]
   [(· +) s (@ hole (@ (List s) Nat))]
   [(· -) s (@ hole (@ (List r) Nat))]
   [(· ○) s (@ hole Nat)]))

(module+ test
  (redex-judgment-holds-chk
   (neg-stage-vector Δlist)
   [· s hole]
   [(· ⊕) s (@ hole (@ (List r) Nat))]
   [(· +) s (@ hole (@ (List r) Nat))]
   [(· -) s (@ hole (@ (List s) Nat))]
   [(· ○) s (@ hole Nat)]))

(begin ;; positivity/negativity of term variables

  (define-judgment-form cicL
    #:mode (pos-term I I I)
    #:contract (pos-term Δ x e)

    [(side-condition (not-free-in x e))
     -----------------
     (pos-term Δ x e)]

    [(side-condition (alpha-equivalent? cicL x e))
     -----------------
     (pos-term Δ x e)]

    [(neg-term Δ x t_0) (pos-term Δ x t_1)
     ----------------------------------
     (pos-term Δ x (Π (x : t_0) t_1))]

    [(where Θ_p (take-parameters Δ D Θ))
     (where Θ_a (take-indicies   Δ D Θ))
     (where V (Δ-ref-polarities Δ D))
     (pos-term-vector Δ V x Θ_p)
     (side-condition (not-free-in x Θ_a))
     ----------------------------------
     (pos-term Δ x (in-hole Θ (D S)))])

  (define-judgment-form cicL
    #:mode (neg-term I I I)
    #:contract (neg-term Δ x e)

    [(side-condition (not-free-in x e))
     ------------------
     (neg-term Δ x e)]

    [(pos-term Δ x t_0) (neg-term Δ x t_1)
     ----------------------------------
     (neg-term Δ x (Π (y : t_0) t_1))]

    [(where Θ_p (take-parameters Δ D Θ))
     (where Θ_a (take-indicies   Δ D Θ))
     (where V (Δ-ref-polarities Δ D))
     (neg-term-vector Δ V x Θ_p)
     (side-condition (not-free-in x Θ_a))
     ----------------------------------
     (neg-term Δ x (in-hole Θ (D S)))])

  (define-judgment-form cicL
    #:mode (pos-term-vector I I I I)
    #:contract (pos-term-vector Δ V x Θ)

    [------------------------------
     (pos-term-vector Δ · x hole)]

    [(pos-term Δ x e)
     (pos-term-vector Δ V x Θ)
     ------------------------------------
     (pos-term-vector Δ (V ⊕) x (@ Θ e))]

    [(pos-term Δ x e)
     (pos-term-vector Δ V x Θ)
     ------------------------------------
     (pos-term-vector Δ (V +) x (@ Θ e))]

    [(neg-term Δ x e)
     (pos-term-vector Δ V x Θ)
     ------------------------------------
     (pos-term-vector Δ (V -) x (@ Θ e))]

    [(side-condition (not-free-in x e))
     (pos-term-vector Δ V x Θ)
     ------------------------------------
     (pos-term-vector Δ (V ○) x (@ Θ e))])

  (define-judgment-form cicL
    #:mode (neg-term-vector I I I I)
    #:contract (neg-term-vector Δ V x Θ)

    [------------------------------
     (neg-term-vector Δ · x hole)]

    [(neg-term Δ x e)
     (neg-term-vector Δ V x Θ)
     ------------------------------------
     (neg-term-vector Δ (V ⊕) x (@ Θ e))]

    [(neg-term Δ x e)
     (neg-term-vector Δ V x Θ)
     ------------------------------------
     (neg-term-vector Δ (V +) x (@ Θ e))]

    [(pos-term Δ x e)
     (neg-term-vector Δ V x Θ)
     ------------------------------------
     (neg-term-vector Δ (V -) x (@ Θ e))]

    [(side-condition (not-free-in x e))
     (neg-term-vector Δ V x Θ)
     ------------------------------------
     (neg-term-vector Δ (V ○) x (@ Θ e))]))

(module+ test
  (redex-judgment-holds-chk
   (pos-term Δlist)
   [x Prop]
   [x x]
   [x (Π (x : Prop) Set)]
   [x (Π (x : Set) (@ List x))]))

(module+ test
  (redex-judgment-holds-chk
   (neg-term Δlist)
   [x Prop]
   [x (Π (x : Prop) Set)]
   [x (Π (y : (@ List x)) Nat)]))

(module+ test
  (redex-judgment-holds-chk
   (pos-term-vector Δlist)
   [· x hole]
   [(· ⊕) x (@ hole (@ List x))]
   [(· +) x (@ hole (@ List x))]
   [(· -) x (@ hole (Π (y : (@ List x)) Nat))]
   [(· ○) x (@ hole Nat)]))

(module+ test
  (redex-judgment-holds-chk
   (neg-term-vector Δlist)
   [· s hole]
   [(· ⊕) x (@ hole (Π (y : (@ List x)) Nat))]
   [(· +) x (@ hole (Π (y : (@ List x)) Nat))]
   [(· -) x (@ hole (@ List x))]
   [(· ○) x (@ hole Nat)]))

(begin ;; positivity of contexts
  ;; I don't think we need rules for let-contexts (i.e. (Γ (x = e : t)))

  (define-judgment-form cicL
    #:mode (pos-context I I I I)
    #:contract (pos-context Δ Γ V (x ...))

    [-----------------------
     (pos-context Δ Γ · ())]

    [(pos-term Δ x t)
     (pos-context Δ Γ V (x_0 ...))
     ----------------------------------------------
     (pos-context Δ (Γ (y : t)) (V ⊕) (x_0 ... x))]

    [(pos-term Δ x t)
     (pos-context Δ Γ V (x_0 ...))
     ----------------------------------------------
     (pos-context Δ (Γ (y : t)) (V +) (x_0 ... x))]

    [(neg-term Δ x t)
     (pos-context Δ Γ V (x_0 ...))
     ----------------------------------------------
     (pos-context Δ (Γ (y : t)) (V -) (x_0 ... x))]

    [(side-condition (not-free-in x t))
     (pos-context Δ Γ V (x_0 ...))
     ----------------------------------------------
     (pos-context Δ (Γ (y : t)) (V ○) (x_0 ... x))]))

(module+ test
 (redex-judgment-holds-chk
  (pos-context Δlist)
  [· · ()]
  [(· (y : (Π (y : Nat) (@ List x)))) (· ⊕) (x)]
  [(· (y : (Π (y : Nat) (@ List x)))) (· +) (x)]
  [(· (y : (Π (y : (@ List x)) Nat))) (· -) (x)]
  [(· (y : Nat)) (· ○) (x)]))

(begin ;; strict positivity

  (define-judgment-form cicL
    #:mode (strict-positivity I I I)
    #:contract (strict-positivity Δ D t)

    [(side-condition (not-free-in D t))
     --------------------------
     (strict-positivity Δ D t)]

    [(side-condition (not-free-in D Θ))
     --------------------------------------
     (strict-positivity Δ D (in-hole Θ (D ∞)))]

    [(side-condition (not-free-in D Θ))
     --------------------------------------
     (strict-positivity Δ D (in-hole Θ D))]

    [(side-condition (not-free-in D t_1))
     (strict-positivity Δ D t_2)
     ------------------------------------------
     (strict-positivity Δ D (Π (x : t_1) t_2))]

    [(side-condition (Δ-in-dom Δ D_0))
     (where V (Δ-ref-polarities Δ D_0))
     (where Θ_p (take-parameters Δ D_0 Θ))
     (where Θ_a (take-indicies   Δ D_0 Θ))
     (side-condition (not-free-in D Θ_a))
     (strict-positivity-vector Δ V D Θ_p)
     ------------------------------------------
     (strict-positivity Δ D (in-hole Θ (D_0 ∞)))])

  (define-judgment-form cicL
    #:mode (strict-positivity-vector I I I I)
    #:contract (strict-positivity-vector Δ V D Θ)

    [--------------------------------------
     (strict-positivity-vector Δ · D hole)]

    [(strict-positivity Δ D e)
     (strict-positivity-vector Δ V D Θ)
     ---------------------------------------------
     (strict-positivity-vector Δ (V ⊕) D (@ Θ e))]

    [(side-condition (not-free-in D e))
     (strict-positivity-vector Δ V D Θ)
     ---------------------------------------------
     (strict-positivity-vector Δ (V _) D (@ Θ e))]))

(module+ test
  (redex-judgment-holds-chk
   (strict-positivity Δlist)
   [Nat Prop]
   [Nat (Nat ∞)]
   [List (@ (List ∞) (Nat ∞))]
   [Nat (Π (x : Set) (Nat ∞))]
   [Nat (@ (List ∞) (Nat ∞))]))

(module+ test
  (redex-judgment-holds-chk
   (strict-positivity-vector Δlist)
   [· Nat hole]
   [(· ⊕) Nat (@ hole (@ (List ∞) (Nat ∞)))]
   [(· +) List (@ hole (Nat ∞))]
   [(· -) List (@ hole (Nat ∞))]
   [(· ○) List (@ hole (Nat ∞))]
   [((· ⊕) -) Nat (@ (@ hole (@ (List ∞) (Nat ∞))) Prop)]))

(begin ;; strict positivity

  ;; t satisfied the strict positivity condition for D
  ;; translated from https://coq.inria.fr/doc/Reference-Manual006.html#Cic-inductive-definitions
  (define-judgment-form cicL
    #:mode (strict-positivity-cond I I I I)
    #:contract (strict-positivity-cond Δ Γ D t)

    [(side-condition (not-free-in D Θ))
     --------------------------------------------- "SP-App"
     (strict-positivity-cond Δ Γ D (in-hole Θ D))]

    [(occurs-strictly-positively Δ Γ D t_0)
     (strict-positivity-cond Δ Γ D t_1)
     ------------------------------------------------- "SP-Π"
     (strict-positivity-cond Δ Γ D (Π (x : t_0) t_1))])

  ;; D occurs strictly positively in t
  (define-judgment-form cicL
    #:mode (occurs-strictly-positively I I I I)
    #:contract (occurs-strictly-positively Δ Γ D t)

    [(side-condition (not-free-in D t))
     ------------------------------------- "OSP-NotIn"
     (occurs-strictly-positively Δ Γ D t)]

    [(normalize Δ Γ t (in-hole Θ D))
     (side-condition (not-free-in D Θ))
     ------------------------------------- "OSP-NotArg"
     (occurs-strictly-positively Δ Γ D t)]

    [(normalize Δ Γ t (Π (x : t_0) t_1))
     (side-condition (not-free-in D t_0))
     (occurs-strictly-positively Δ Γ D t_1)
     ------------------------------------- "OSP-Π"
     (occurs-strictly-positively Δ Γ D t)]

    [(normalize Δ Γ t (in-hole Θ D_i))
     (where (D_!_0 D_!_0) (D D_i)) ;; D_i is a different inductive type
     (side-condition (Δ-in-dom Δ D_i))
     (where n (Δ-ref-parameter-count Δ D_i))
     ;; D not free in the index arguments of D_i
     (side-condition (not-free-in D (Θ-drop Θ n)))
     ;; Instantiated types of the constructors for D_i satisfy the nested positivity condition for D
     (where Θ_p (Θ-take Θ n))
     (where ((c : t_c) ...) (Δ-ref-constructor-map Δ D_i))
     (nested-positivity-condition Δ Γ D D_i (instantiate t_c Θ_p)) ...
     ------------------------------------- "OSP-Ind"
     (occurs-strictly-positively Δ Γ D t)])

  ;; The type t of a constructor for D_i satisfied the nested positivity condition for D
  (define-judgment-form cicL
    #:mode (nested-positivity-condition I I I I I)
    #:contract (nested-positivity-condition Δ Γ D D_i t)

    [(side-condition (Δ-in-dom Δ D_i))
     (where n (Δ-ref-parameter-count Δ D_i))
     (side-condition (not-free-in D (Θ-drop Θ n)))
     -------------------------------------------------------- "NPC-App"
     (nested-positivity-condition Δ Γ D D_i (in-hole Θ D_i))]

    [(occurs-strictly-positively Δ Γ D t_0)
     (nested-positivity-condition Δ Γ D D_i t_1)
     ---------------------------------------------------------- "NPC-Π"
     (nested-positivity-condition Δ Γ D D_i (Π (x : t_0) t_1))]))

(module+ test
  (redex-judgment-holds-chk
   (strict-positivity-cond Δnb ·)
   [Bool Bool]
   [Nat Nat]
   [Nat (Π (x : Nat) Nat)]))

(begin ;; simple types

  (define-judgment-form cicL
    #:mode (simple I I)
    #:contract (simple Δ t)

    [(side-condition (no-free-variables? Δ t))
     ------------- "s-empty"
     (simple Δ t)]

    [(simple Δ t_1) (simple Δ t_2)
     ----------------------------- "s-prod"
     (simple Δ (Π (x : t_1) t_2))]

    [(side-condition (Δ-in-dom Δ D))
     (where V (Δ-ref-polarities Δ D))
     (where Θ_p (take-parameters Δ D Θ))
     (where Θ_a (take-indicies   Δ D Θ))
     (side-condition (no-free-stage-vars (in-hole D Θ_a))) ;; need smth to plug the hole in
     (simple-vector Δ V Θ_p)
     ----------------------------- "s-ind"
     (simple Δ (in-hole Θ (D S)))])

  (define-judgment-form cicL
    #:mode (simple-vector I I I)
    #:contract (simple-vector Δ V Θ)

    [------------------------- "sv-empty"
     (simple-vector Δ · hole)]

    [(side-condition (no-free-stage-vars t))
     (simple-vector Δ V Θ)
     -------------------------------- "sv-inv"
     (simple-vector Δ (V ○) (@ Θ t))]

    [(simple Δ t)
     (simple-vector Δ V Θ)
     -------------------------------- "sv-ninv"
     (simple-vector Δ (V _) (@ Θ t))]))

(module+ test
  (redex-judgment-holds-chk
   (simple Δlist)
   [(Π (x : (@ (List s) (Nat s))) (Π (y : (Nat ∞)) (Π (z : (@ (List ∞) (Nat s))) (Nat ∞))))]))

(begin ;; match aux

  ;; Can an inductive type D that lives in U_A be eliminated to some type that lives in U_B?
  ;; NB: Omitting the prod rule as that rule is used to just "type checks" the motive, which we do
  ;; separately.
  ;; This judgment is only responsible for checking the universes
  (define-judgment-form cicL
    #:mode (elimable I I I I)
    #:contract (elimable Δ D U_A U_B)

    [(side-condition ,(not (eq? (term U_1) (term Prop))))
     ----------------------- "Set&Type"
     (elimable Δ D U_1 U_2)]

    [------------------------- "Prop"
     (elimable Δ D Prop Prop)]

    [(where () (Δ-ref-constructor-map Δ D))
     ---------------------- "Prop-extended-empty"
     (elimable Δ D Prop U)]

    [(where ((c : (in-hole Ξ (in-hole Θ_c D)))) (Δ-ref-constructor-map Δ D))
     (where ((_ : Prop) ...) (Ξ-flatten Ξ))
     ---------------------- "Prop-extended-singleton"
     (elimable Δ D Prop U)])

  (define-judgment-form cicL
    #:mode (check-motive I I I I I I)
    #:contract (check-motive Δ Γ t D Θ e)

    [(where Ξ_D (Δ-ref-index-Ξ Δ D Θ_p))
     ;; check that the motive matches the inductive index telescope, i.e., the telescope sans parameters.
     ;; TODO: Check subtyping between Ξ_D, rather than α-equiv?
     (type-infer Δ Γ e (in-hole Ξ_D (Π (x : t_D) U_B)))
     (subtype Δ Γ t_D (Ξ-apply Ξ_D (in-hole Θ_p D)))
     ;; Check that this is a valid elimination sort
     ;; TODO: Test = type
     (type-infer Δ Γ t_I U_A)
     (elimable Δ D U_A U_B)
     -------------------------------
     (check-motive Δ Γ t_I D Θ_p e)])

  (define-judgment-form cicL
    #:mode (check-methods I I I I I I)
    #:contract (check-methods Δ Γ D t Θ (e ...))

    [(where (c ..._1) (Δ-ref-constructors Δ D))
     (where (Ξ_c ..._1) ((Δ-constructor-ref-index-Ξ Δ c Θ) ...))
     (type-check Δ Γ e (in-hole Ξ_c t)) ...
     ----------------------------------
     (check-methods Δ Γ D t Θ (e ...))]))

(begin ;; guard condition

  ;; Check that the body of f, e, is guarded w.r.t y, an inductive argument of type D, with
  ;; accumulated recursive arguments (x ...).
  (define-judgment-form cicL
    #:mode (guard I I I I I I)
    #:contract (guard Δ y D f (x ...) e)

    [(where #t (not-free-in f e))
     ---------------------- "Guard-NotIn"
     (guard Δ y D f any e)]

    [(in x any)
     (where (e ...) (Θ-flatten Θ))
     (guard Δ y D f any e) ...
     -------------------------- "Guard-Rec"
     (guard Δ y D f any (@ f (in-hole Θ x)))]

    [(guard Δ y D f any e_1)
     (guard Δ y D f any e_2)
     ----------------------------------------------------------
     (guard Δ y D (name f e_!_1) any (@ (name e_1 e_!_1) e_2))]

    [(guard Δ y D f any t)
     (guard Δ y D f any e)
     ----------------------------------
     (guard Δ y D f any (λ (x : t) e))]

    [(guard Δ y D f any t)
     (guard Δ y D f any e)
     ----------------------------------
     (guard Δ y D f any (Π (x : t) e))]

    [(guard Δ y D f any e_1)
     (guard Δ y D f any t)
     (guard Δ y D f any e_2)
     ----------------------------------
     (guard Δ y D f any (let (x = e_1 : t) e_2))]

    [(guard Δ y D f any e)
     (guard Δ y D f any e_motive)
     (guard Δ y D f any e_methods) ...
     ------------------------------------------------------
     (guard Δ y D f any (case e e_motive (e_methods ...)))]

    [(where (in-hole Θ x_0) e)
     (in x_0 (x ... y))
     (where (e_j ...) (Θ-flatten Θ))
     (guard Δ y D f (x ...) e_j) ...
     (guard Δ y D f (x ...) e_motive)
     ;; structurally smaller variables.
     (where (((x_more ...) e_body) ...) (split-methods Δ D any))
     (guard Δ y D f (x ... x_more ...) e_body) ...
     ---------------------------------------------- "Guard-CaseSmaller"
     (guard Δ y D f (x ...) (case e e_motive any))])

  ;; Splits the methods into their structurally smaller arguments and the body of the method
  (define-metafunction cicL
    split-methods : Δ D (e ...) -> (((x ...) e) ...)
    [(split-methods Δ D (e ..._0))
     ((split-method D n e) ...)
     (where (c ..._0) (Δ-ref-constructors Δ D))
     (where (n ..._0) ((Δ-constructor-ref-non-parameter-count Δ c) ...))])

  ;; Splits a method into its structurally smaller arguments and the body of the method, where the
  ;; structurally smaller arguments are the first n arguments
  ;; NB: Relies on clause order
  (define-metafunction cicL
    split-method : D n e -> ((x ...) e)
    [(split-method D 0 e)
     (() e)]
    [(split-method D n (λ (x : t) e))
     ((x x_r ...) e_r)
     (side-condition (term (free-in D t)))
     (where ((x_r ...) e_r) (split-method D ,(sub1 (term n)) e))]
    [(split-method D n (λ (x : t) e))
     ((x_r ...) e_r)
     (side-condition (term (not-free-in D t)))
     (where ((x_r ...) e_r) (split-method D ,(sub1 (term n)) e))])

  ;; Does e terminate?
  (define-judgment-form cicL
    #:mode (terminates I I)
    #:contract (terminates Δ e)

    [(Δ-type-in Δ D _)
     (guard Δ y D f () e)
     -----------------------------------------------------
     (terminates Δ (fix f : (Π (x : (in-hole Θ D)) t) (λ (y : (in-hole Θ D)) e)))]))

;; ------------------------------------------------------------------------
;; Vital meta-functions

(begin ;; stages
  ;; the base of a stage
  (define-metafunction cicL
    base : S -> S
    [(base (^ S)) (base S)]
    [(base s) s])

  ;; free stage variables
  (define-metafunction cicL
    no-free-stage-vars : e -> #t or #f
    [(no-free-stage-vars (λ (x : t) e))
     ,(and (term (no-free-stage-vars t))
           (term (no-free-stage-vars e)))]

    [(no-free-stage-vars (@ e_0 e_1))
     ,(and (term (no-free-stage-vars e_0))
           (term (no-free-stage-vars e_1)))]

    [(no-free-stage-vars (Π (x : t_0) t_1))
     ,(and (term (no-free-stage-vars t_0))
           (term (no-free-stage-vars t_1)))]

    [(no-free-stage-vars (let (x = e_0 : t) e_1))
     ,(and (term (no-free-stage-vars e_0))
           (term (no-free-stage-vars t))
           (term (no-free-stage-vars e_1)))]

    [(no-free-stage-vars (case e_0 e_1 (e ...)))
     ,(and (term (no-free-stage-vars e_0))
           (term (no-free-stage-vars e_1))
           (andmap values (term ((no-free-stage-vars e) ...))))]

    [(no-free-stage-vars (fix f : t e))
     ,(and (term (no-free-stage-vars t))
           (term (no-free-stage-vars e)))]

    [(no-free-stage-vars (D S))
     #f
     (where s (base S))]

    [(no-free-stage-vars _) #t])

  ;; inductive types annotated with ∞ only
  (define-metafunction cicL
    full-types-only : e -> #t or #f
    [(full-types-only (λ (x : t) e))
     ,(and (term (full-types-only t))
           (term (full-types-only e)))]

    [(full-types-only (@ e_0 e_1))
     ,(and (term (full-types-only e_0))
           (term (full-types-only e_1)))]

    [(full-types-only (Π (x : t_0) t_1))
     ,(and (term (full-types-only t_0))
           (term (full-types-only t_1)))]

    [(full-types-only (let (x = e_0 : t) e_1))
     ,(and (term (full-types-only e_0))
           (term (full-types-only t))
           (term (full-types-only e_1)))]

    [(full-types-only (case e_0 e_1 (e ...)))
     ,(and (term (full-types-only e_0))
           (term (full-types-only e_1))
           (andmap values (term ((full-types-only e) ...))))]

    [(full-types-only (fix f : t e))
     ,(and (term (full-types-only t))
           (term (full-types-only e)))]

    [(full-types-only (D ∞)) #t]
    [(full-types-only (D *)) #f]
    [(full-types-only (D °)) #f]
    [(full-types-only (D _)) #f]
    [(full-types-only    _ ) #t])

  ;; stage erasure to bare terms
  (define-metafunction cicL
    erase-to-bare : Δ e -> e
    [(erase-to-bare Δ D)
     (D °)
     (where #t (Δ-in-dom Δ D))]
    [(erase-to-bare Δ (D S))
     (D °)]
    [(erase-to-bare Δ (D *))
     (D °)]
    [(erase-to-bare Δ (λ (x : t) e))
      (λ (x : t) e)
      (where e (erase-to-bare Δ e))]
    [(erase-to-bare Δ (@ e_1 e_2))
      (@ e_1 e_2)
      (where e_1 (erase-to-bare Δ e_1))
      (where e_2 (erase-to-bare Δ e_2))]
    [(erase-to-bare Δ (Π (x : t_1) t_2))
      (Π (x : t_1) t_2)
      (where t_1 (erase-to-bare Δ t_1))
      (where t_2 (erase-to-bare Δ t_2))]
    [(erase-to-bare Δ (let (x = e_1 : t) e_2))
      (let (x = e_1 : t) e_2)
      (where e_1 (erase-to-bare Δ e_1))
      (where e_2 (erase-to-bare Δ e_2))]
    [(erase-to-bare Δ (case e_1 e_2 (e_3 ...)))
      (case e_1 e_2 constr)
      (where e_1 (erase-to-bare Δ e_1))
      (where constr ,(map (lambda (e) (term (erase-to-bare Δ e))) (term (e_3 ...))))]
    [(erase-to-bare Δ (fix f : t e))
      (fix f : t e)
      (where e (erase-to-bare Δ e))]
    [(erase-to-bare Δ e) e])

  ;; stage erasure to position terms
  (define-metafunction cicL
    erase-to-position : Δ s e -> e
    [(erase-to-position Δ s D)
     (D °)
     (where #t (Δ-in-dom Δ D))]
    [(erase-to-position Δ s (D S))
     ,(if (eq? (term s) (term (base S)))
          (term (D *))
          (term (D °)))]
    [(erase-to-position Δ s (λ (x : t) e))
      (λ (x : t) e)
      (where e (erase-to-position Δ s e))]
    [(erase-to-position Δ s (@ e_1 e_2))
      (@ e_1 e_2)
      (where e_1 (erase-to-position Δ s e_1))
      (where e_2 (erase-to-position Δ s e_2))]
    [(erase-to-position Δ s (Π (x : t_1) t_2))
      (Π (x : t_1) t_2)
      (where t_1 (erase-to-position Δ s t_1))
      (where t_2 (erase-to-position Δ s t_2))]
    [(erase-to-position Δ s (let (x = e_1 : t) e_2))
      (let (x = e_1 : t) e_2)
      (where e_1 (erase-to-position Δ s e_1))
      (where e_2 (erase-to-position Δ s e_2))]
    [(erase-to-position Δ (case e_1 e_2 (e_3 ...)))
      (case e_1 e_2 constr)
      (where e_1 (erase-to-position Δ s e_1))
      (where constr ,(map (lambda (e) (term (erase-to-position Δ s e))) (term (e_3 ...))))]
    [(erase-to-position Δ (fix f : t e))
      (fix f : t e)
      (where e (erase-to-position Δ s e))]
    [(erase-to-position Δ e) e]))

(begin ;; V defs
  ;; Get parameter variables where polarity is noninvariant (strictly positive, positive, or negative)
  (define-metafunction cicL
    noninvariant-variables : V ((x : t) ...) -> (x ...)
    [(noninvariant-variables · hole) ()]

    [(noninvariant-variables (V ○) ((x : t) ... _))
     (noninvariant-variables V ((x : t) ...))]

    [(noninvariant-variables (V _) ((x : t) ... (x_0 : t_0)))
     (x_1 ... x_0)
     (where (x_1 ...) (noninvariant-variables V ((x : t) ...)))])

  ;; Get parameter variables where polarity is strictly positive
  (define-metafunction cicL
    strictly-positive-variables : V ((x : t) ...) -> (x ...)
    [(strictly-positive-variables · hole) ()]

    [(strictly-positive-variables (V ⊕) ((x : t) ... (x_0 : t_0)))
     (x_1 ... x_0)
     (where (x_1 ...) (strictly-positive-variables V ((x : t) ...)))]

    [(strictly-positive-variables (V _) ((x : t) ...))
     (strictly-positive-variables V ((x : t) ...))]))

(begin ;; Γ defs
  ;; Make x : t ∈ Γ a little easier to use, prettier to render
  (define-judgment-form cicL
    #:mode (Γ-in I I O)
    #:contract (Γ-in Γ x t)

    [(where (x any ... : t) (snoc-env-ref Γ x))
     -------------------------------
     (Γ-in Γ x t)]))

(begin ;; Δ defs
  (define-metafunction cicL
    Δ-in-dom : Δ D -> #t or #f
    [(Δ-in-dom Δ D) (snoc-env-in-dom Δ D)])

  (define-metafunction cicL
    Δ-in-constructor-dom : Δ c -> #t or #f
    [(Δ-in-constructor-dom Δ c)
     ,(ormap (lambda (Γ_c) (term (snoc-env-in-dom ,Γ_c c))) (term (Γ_c ...)))
     (where ((_ _ _ _ _ Γ_c) ...) (snoc-env->als Δ))])

  ;; make D : t ∈ Δ a little easier to use, prettier to render
  (define-judgment-form cicL
    #:mode (Δ-type-in I I O)
    #:contract (Δ-type-in Δ D t)

    [(where (D : _ _ t _) (snoc-env-ref Δ D))
     -------------------------------
     (Δ-type-in Δ D t)]

    [(where (D : _ _ t _) (snoc-env-ref Δ D))
     -------------------------------
     (Δ-type-in Δ (D S) t)]

    [(where (D : _ _ t _) (snoc-env-ref Δ D))
     -------------------------------
     (Δ-type-in Δ (D *) t)]

    [(where (D : _ _ t _) (snoc-env-ref Δ D))
     -------------------------------
     (Δ-type-in Δ (D °) t)])

  ;; Return the number of parameters for the inductive type D
  (define-metafunction cicL
    Δ-ref-parameter-count : Δ_0 D_0 -> n
    #:pre (Δ-in-dom Δ_0 D_0)
    [(Δ-ref-parameter-count Δ D)
     n
     (where (D : n _ _ _) (snoc-env-ref Δ D))])

  ;; Return the number of parameters for the inductive type D that has a constructor c_0
  (define-metafunction cicL
    Δ-constructor-ref-parameter-count : Δ_0 c_0 -> n
    #:pre (Δ-in-constructor-dom Δ_0 c_0)
    [(Δ-constructor-ref-parameter-count Δ c)
     n
     (where (D : n _ _ _) (Δ-ref-by-constructor Δ c))])

  ;; Return the number of non-parameters arguments for the constructor c_0
  (define-metafunction cicL
    Δ-constructor-ref-non-parameter-count : Δ_0 c_0 -> n
    #:pre (Δ-in-constructor-dom Δ_0 c_0)
    [(Δ-constructor-ref-non-parameter-count Δ c)
     ,(- (term (Ξ-length Ξ)) (term n))
     (where n (Δ-constructor-ref-parameter-count Δ c))
     (judgment-holds (Δ-constr-in Δ c (in-hole Ξ (in-hole Θ D))))])

  ;; Return the vector of polarities for the inductive type D
  (define-metafunction cicL
    Δ-ref-polarities : Δ_0 D_0 -> V
    #:pre (Δ-in-dom Δ_0 D_0)
    [(Δ-ref-polarities Δ D)
     V
     (where (D : _ V _ _) (snoc-env-ref Δ D))])

  ;; Returns the inductively defined type that x constructs
  (define-metafunction cicL
    Δ-key-by-constructor : Δ_0 c_0 -> D
    #:pre (Δ-in-constructor-dom Δ_0 c_0)
    [(Δ-key-by-constructor Δ c)
     D
     (where (_ ... (D _ _ _ _ Γ_c) _ ...) (snoc-env->als Δ))
     (side-condition (term (snoc-env-in-dom Γ_c c)))])

  (define-metafunction cicL
    Δ-ref-by-constructor : Δ_0 c_0 -> (D : n V t Γ_c)
    #:pre (Δ-in-constructor-dom Δ_0 c_0)
    [(Δ-ref-by-constructor Δ c)
     (snoc-env-ref Δ D)
     (where D (Δ-key-by-constructor Δ c))])

  ;; Returns the constructor map for the inductively defined type D in the signature Δ
  (define-metafunction cicL
    Δ-ref-constructor-map : Δ_0 D_0 -> ((c : t) ...)
    #:pre (Δ-in-dom Δ_0 D_0)
    [(Δ-ref-constructor-map Δ D)
     ,(term (snoc-env->als Γ_c))
     (where (_ _ _ _ _ Γ_c) (snoc-env-ref Δ D))])

  (define-metafunction cicL
    Δ-ref-constructors : Δ_0 D_0 -> (c ...)
    #:pre (Δ-in-dom Δ_0 D_0)
    [(Δ-ref-constructors Δ D)
     (c ...)
     (where ((c _ _) ...) (Δ-ref-constructor-map Δ D))])

  ;; Return the type of the constructor c_i
  (define-metafunction cicL
    Δ-ref-constructor-type : Δ_0 c_0 -> t
    #:pre (Δ-in-constructor-dom Δ_0 c_0)
    [(Δ-ref-constructor-type Δ c)
     t
     (where (_ _ _ _ _ Γ_c) (Δ-ref-by-constructor Δ c))
     (judgment-holds (Γ-in Γ_c c t))])

  ;; Make c : t ∈ Δ a little easier to use, prettier to render
  (define-judgment-form cicL
    #:mode (Δ-constr-in I I O)
    #:contract (Δ-constr-in Δ c t)

    [(side-condition (Δ-in-constructor-dom Δ c))
     (where t (Δ-ref-constructor-type Δ c))
     -------------------------------
     (Δ-constr-in Δ c t)])

  (define-metafunction cicL
    Δ-ref-index-Ξ : Δ_0 D_0 Θ_0 -> Ξ
    #:pre ,(and (term (Δ-in-dom Δ_0 D_0))
                (= (term (Θ-length Θ_0)) (term (Δ-ref-parameter-count Δ_0 D_0))))
    [(Δ-ref-index-Ξ Δ D Θ)
     Ξ
     (where (D : _ _ t _) (snoc-env-ref Δ D))
     (where (in-hole Ξ U) (instantiate t Θ))])

  (define-metafunction cicL
    Δ-constructor-ref-index-Ξ : Δ_0 c_0 Θ_0 -> Ξ
    #:pre ,(and (term (Δ-in-constructor-dom Δ_0 c_0))
                (= (term (Θ-length Θ_0)) (term (Δ-constructor-ref-parameter-count Δ_0 c_0))))
    [(Δ-constructor-ref-index-Ξ Δ c Θ)
     Ξ
     (where t (Δ-ref-constructor-type Δ c))
     (where (in-hole Ξ (in-hole Θ_0 D)) (instantiate t Θ))])

  ;; constructors appear applied to their parameters and indices, but methods expect indices
  ;; create a new application context without the the parameters
  (define-metafunction cicL
    take-indicies : Δ c Θ -> Θ
    [(take-indicies Δ c Θ)
     (Θ-drop Θ n)
     (judgment-holds (Δ-constr-in Δ c t))
     (where n (Δ-constructor-ref-parameter-count Δ c))]
    [(take-indicies Δ D Θ)
     (Θ-drop Θ n)
     (where n (Δ-ref-parameter-count Δ D))])

  (define-metafunction cicL
    take-parameters : Δ_0 D_0 Θ -> Θ
    #:pre (Δ-in-dom Δ_0 D_0)
    [(take-parameters Δ D Θ)
     (Θ-take Θ n)
     (where n (Δ-ref-parameter-count Δ D))]))

(begin ;; aux defs
  (define-metafunction cicL
    Ξ-build : (x : t) ... -> Ξ
    [(Ξ-build)
     hole]
    [(Ξ-build any any_r ...)
     (Π any (Ξ-build any_r ...))])

  (define-metafunction cicL
    Ξ-apply : Ξ e_0 -> (in-hole Θ e_0)
    [(Ξ-apply hole e) e]
    [(Ξ-apply (Π (x : t) Ξ) e)
     (Ξ-apply Ξ (@ e x))])

  ;; Return the list of bindings from Ξ in reverse dependency order
  (define-metafunction cicL
    Ξ-flatten : Ξ -> ((x : t) ...)
    [(Ξ-flatten hole)
     ()]
    [(Ξ-flatten (Π (x : t) Ξ))
     ((x : t) any ...)
     (where (any ...) (Ξ-flatten Ξ))])

  (define-metafunction cicL
    Ξ-length : Ξ -> n
    [(Ξ-length Ξ)
     ,(length (term (Ξ-flatten Ξ)))])

  (define-metafunction cicL
    Ξ-drop : Ξ_0 n_0 -> Ξ
    #:pre ,(<= (term n_0) (term (Ξ-length Ξ_0)))
    [(Ξ-drop Ξ 0)
     Ξ]
    [(Ξ-drop (Π _ Ξ) n)
     (Ξ-drop Ξ ,(sub1 (term n)))])

  (define-metafunction cicL
    Ξ-take : Ξ_0 n_0 -> Ξ
    #:pre ,(<= (term n_0) (term (Ξ-length Ξ_0)))
    [(Ξ-take Ξ 0)
     hole]
    [(Ξ-take (Π (x : t) Ξ) n)
     (Π (x : t) (Ξ-take Ξ ,(sub1 (term n))))])

  ;; Return the list of operands from Θ in reverse dependency order
  (define-metafunction cicL
    Θ-flatten : Θ -> (e ...)
    [(Θ-flatten hole)
     ()]
    [(Θ-flatten (@ Θ e))
     (any ... e)
     (where (any ...) (Θ-flatten Θ))])

  (define-metafunction cicL
    Θ-length : Θ -> n
    [(Θ-length Θ)
     ,(length (term (Θ-flatten Θ)))])

  (define-metafunction cicL
    Θ-drop : Θ_0 n_0 -> Θ
    #:pre ,(<= (term n_0) (term (Θ-length Θ_0)))
    [(Θ-drop Θ 0)
     Θ]
    [(Θ-drop (in-hole Θ (@ hole e)) n)
     (Θ-drop Θ ,(sub1 (term n)))])

  (define-metafunction cicL
    Θ-take : Θ_0 n_0 -> Θ
    #:pre ,(<= (term n_0) (term (Θ-length Θ_0)))
    [(Θ-take Θ 0)
     hole]
    [(Θ-take (in-hole Θ (@ hole e)) n)
     (in-hole (Θ-take Θ ,(sub1 (term n))) (@ hole e))])

  ;; Instantiate a Π type
  (define-metafunction cicL
    instantiate : t Θ -> t
    [(instantiate t hole)
     t]
    [(instantiate (Π (x : t) t_1) (in-hole Θ (@ hole e)))
     (instantiate (substitute t_1 x e) Θ)]))

(module+ test
  (redex-chk
   (Δ-in-constructor-dom · x) #f)

  (redex-chk
   #:lang cicL
   (Ξ-length hole) 0
   (Ξ-length (Π (x : Set) hole)) 1
   (Δ-ref-constructor-type Δnb z) Nat
   (Δ-ref-constructor-type Δnb s) (Π (x : Nat) Nat)
   (Δ-ref-index-Ξ Δnb Nat hole) hole
   (Δ-ref-constructor-map Δnb Nat) ((z : Nat) (s : (Π (x : Nat) Nat)))

   #:m hole (Δ-constructor-ref-index-Ξ Δnb z hole)
   #:m (Π (x : Nat) hole) (Δ-constructor-ref-index-Ξ Δnb s hole)
   #:m hole (Δ-constructor-ref-index-Ξ Δlist nil (@ hole Nat))

   #:m (Π (x_2 : Nat) (Π (x_3 : (@ List Nat)) hole)) (Δ-constructor-ref-index-Ξ Δlist cons (@ hole Nat))
   (Ξ-apply hole Nat) Nat
   (in-hole hole (Π (x : (Ξ-apply hole Nat)) Set)) (Π (x : Nat) Set)
   (Δ-key-by-constructor Δnb z) Nat))
