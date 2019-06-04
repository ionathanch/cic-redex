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
  (e t ::= c x (λ (x : t) e) (@ e e) (I@ d t ...) (C@ c e ...) (Π (x : t) t) U (let (x = e : t) e) (case e e (e ...)) (fix f : t e))
  (d :: = (D °) (D *) (D S) D)  ;; inductive types with size annotations: bare, position, stage; D == (D ∞)
  (Γ ::= · (Γ (x : t)) (Γ (x = e : t)))
  (Δ ::= · (Δ (D : n V t Γ)))

  (v ::= ⊕ + - ○)  ;; strictly positive, positive, negative, invariant polarities
  (V ::= (v ...))   ;; vector of polarities for parameters of inductive types

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
    (· (False : 0 () Prop ·)))

  (define-term Δ01
    (Δ0 (Unit : 0 () Prop (· (tt : (I@ Unit))))))

  (define-term Δb
    (Δ01 (Bool : 0 () Set ((· (true : (I@ Bool))) (false : (I@ Bool))))))

  (define-term Δnb
    (Δb (Nat : 0 () Set ((· (z : (I@ Nat))) (s : (Π (x : (I@ Nat)) (I@ Nat)))))))

  ;; Tests parameters
  (define-term Δlist
    (Δnb (List : 1 (⊕) (Π (A : Set) Set)
                ((· (nil : (Π (A : Set) (I@ List A))))
                 (cons : (-> (A : Set) (a : A) (ls : (I@ List A)) (I@ List A)))))))

  ;; Check that all constructors have explicit parameter declarations; implicit is surface sugar
  (define-term Δbadlist
    (Δnb (List : 1 (⊕) (Π (A : Set) Set)
                ((· (nil : (I@ List A)))
                 (cons : (-> (a : A) (ls : (I@ List A)) (I@ List A)))))))

  ;; Shorthand terms for fully-applied inductive types and constructors
  (define-term IUnit     (I@ Unit))
  (define-term IBool     (I@ Bool))
  (define-term INat      (I@ Nat))
  (define-term IListNat  (I@ List (I@ Nat)))
  (define-term Ctt       (C@ tt))
  (define-term Ctrue     (C@ true))
  (define-term Cfalse    (C@ false))
  (define-term Cz        (C@ z))
  (define-term CnilNat   (C@ nil (I@ Nat)))

  (define-term subn
    (fix f : (Π (x : INat) INat)
         (λ (x : INat)
           (case x (λ (x : INat) INat) (Cz (λ (x : INat) (@ f x)))))))

  (define-term plus
    (fix add : (Π (n : INat) (Π (m : INat) INat))
      (λ (n : INat)
        (λ (m : INat)
          (case n (λ (x : INat) INat)
            (m
             (λ (x : INat)
               (C@ s (@ (@ add x) m)))))))))

  ;; ill-typed but well-formed
  (define-term subn-bad1
    (fix f : (Π (x : INat) INat)
         (λ (x : INat)
           (case x (λ (x : INat) INat) (Cz (λ (x : INat) (@ f z)))))))

  (define-term subn-bad2
    (fix f : (Π (x : INat) INat)
         (λ (A : Set)
           (λ (x : INat)
             (case x (λ (x : INat) INat) (Cz (λ (x : INat) (@ f x))))))))

  (define-term Ω
    (fix f : (Π (x : INat) INat)
         (λ (x : INat)
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
   #:m (in-hole Θ Nat) Nat
   #:m (in-hole Ξ (in-hole Θ Nat)) (Π (x : Nat) Nat)
   #:m (in-hole hole (Π (x : (in-hole Θ D)) U)) (Π (x : Nat) Set)
   #:m (in-hole Ξ_D (Π (x : (in-hole Θ D)) U)) (Π (x : Nat) Set)))

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
       (--> (case (C@ c_i e ...) _ (e_0 ... e_n))
            (in-hole Θ_i e_i)
            (where #t (Δ-in-constructor-dom Δ c_i))
            (where/hidden e_i (select-method Δ c_i e_0 ... e_n))
            (where (_ (e_a ...)) (take-parameters-indices Δ c_i (e ...)))
            (where Θ_i (Θ-build (e_a ...)))
            "ι1")
       (--> (@ (name e_f (fix f : t_f (λ (x : t) e))) (name e_a (C@ c e_c ...)))
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
   (reduce · · (in-hole (@ hole z) (λ (x : Nat) Nat))) Nat
   (reduce Δnb · (case Cz (λ (x : Nat) Nat) (Cz (λ (x : Nat) x)))) Cz
   (reduce Δlist · (case (C@ nil Nat) (λ (ls : (I@ List Nat)) Bool) (true false))) true
   (reduce Δnb (· (x : Nat)) (@ subn x)) (@ subn x)
   (reduce Δnb · (@ subn Cz)) Cz
   (reduce Δnb · (@ subn (C@ s Cz))) Cz
   (reduce Δnb · (@ (@ plus Cz) Cz)) Cz
   (reduce Δnb · (@ (@ plus (C@ s Cz)) Cz)) (C@ s Cz)
   (reduce Δnb · (@ (@ plus Cz) (C@ s Cz))) (C@ s Cz)
   (reduce Δnb · (@ (@ plus (C@ s Cz)) (C@ s Cz))) (C@ s (C@ s Cz))))

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
     #:eq Cz (@ subn Cz)
     #:eq Cz (@ subn (C@ s Cz))
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
  [(normalize Δ Γ e_0 (I@ d_0 e_pi0 ...))
   (normalize Δ Γ e_1 (I@ d_1 e_pi1 ...))
   (annot-type d_0 (D S_0))
   (annot-type d_1 (D S_1))
   (<=S S_0 S_1)
   (where ((e_p0 ...) (e_i0 ...)) (take-parameters-indices Δ D (e_pi0 ...)))
   (where ((e_p1 ...) (e_i1 ...)) (take-parameters-indices Δ D (e_pi1 ...)))
   (where (v ...) (Δ-ref-polarities Δ D))
   (subtype-polarity Δ Γ v e_p0 e_p1) ...
   (convert Δ Γ e_i0 e_i1) ...
   ---------------------- "≼-D"
   (subtype Δ Γ e_0 e_1)])

(define-judgment-form cicL
  #:mode (subtype-polarity I I I I I)
  #:contract (subtype-polarity Δ Γ v e e)

  [(convert Δ Γ e_0 e_1)
   --------------------------------- "vst-inv"
   (subtype-polarity Δ Γ ○ e_0 e_1)]

  [(subtype Δ Γ e_0 e_1)
   ---------------------------------- "vst-strict-pos"
   (subtype-polarity Δ Γ ⊕ e_0 e_1)]

  [(subtype Δ Γ e_0 e_1)
   --------------------------------- "vst-pos"
   (subtype-polarity Δ Γ + e_0 e_1)]

  [(subtype Δ Γ e_1 e_0)
   --------------------------------- "vst-neg"
   (subtype-polarity Δ Γ - e_0 e_1)])

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
   [(I@ Nat) (I@ Nat)]
   [(I@ (Nat S)) (I@ Nat)]
   [(I@ (Nat S)) (I@ (Nat ∞))]
   [(I@ Nat) (I@ (Nat ∞))]
   [(I@ (Nat ∞)) (I@ Nat)]
   [(I@ (Nat ∞)) (I@ (Nat ∞))]
   [(I@ (List S) INat) (I@ (List (^ S)) INat)]))

(module+ test
  (redex-judgment-holds-chk
   (subtype-polarity · ·)
   [⊕ Prop Set]
   [+ Prop Set]
   [- Set Prop]
   [○ Prop Prop]))

;; ------------------------------------------------------------------------
;; Typing

(begin ;; well-formed environment

  (define-judgment-form cicL
    #:mode (valid-parameters I I I)
    #:contract (valid-parameters n t t)

    [-------------------------------
     (valid-parameters 0 t_0 t_1)]

    [(valid-parameters ,(sub1 (term n)) t_0 t_1)
     -------------------------------------------------------
     (valid-parameters n (Π (x : t) t_0) (Π (y : t) t_1))])

  (define-judgment-form cicL
    #:mode (constructor-type I I I)
    #:contract (constructor-type Δ D t)

    [(full-type d D)
     -----------------------------------------
     (constructor-type Δ D (I@ d e ...))]

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
    #:contract (valid-constructor Δ (c : t))

    [(where (in-hole Ξ_c (I@ d e ...)) t_c) (full-type d D)
     (valid-parameters n t_c t_D) ;; constructor has same parameters as inductive type
     (side-condition (full-types-only t_c)) ;; I5
     (type-infer Δ (· (D : t_D)) (I@-to-@ D t_c) U_c) ;; I2
     (constructor-type Δ D t_c) ;; I4
     ;; Positivity conditions
     (where Ξ_p (Ξ-take-parameters Δ_0 c Ξ_c))
     (where Ξ_i (Ξ-take-indices    Δ_0 c Ξ_c))
     (where ((x_p : _) ...) (Ξ-flatten Ξ_p))
     (where (x_ni ...) (pos-neg-variables V Ξ_p))
     (where (x_sp ...) (strictly-positive-variables V Ξ_p))
     (pos-context Δ_0 V (x_p ...) Ξ_c) ;; I6
     (side-condition (all ((not-free-in x_ni (e ...)) ...))) ;; I7
     (strict-positivity-product Δ_0 x_sp Ξ_i) ... ;; I9
     --------------------------------------------------------------------------------------
     (valid-constructor (name Δ_0 (Δ (D : n V (name t_D (in-hole Ξ_D U_D)) _))) (c : t_c))])

  ;; Under global declarations Δ, is the term environment well-formed?
  (define-judgment-form cicL
    #:mode (wf I I)
    #:contract (wf Δ Γ)

    [--------- "W-Empty"
     (wf · ·)]

    [(wf Δ Γ)
     #;(type-infer Δ Γ t U)
     ------------------- "W-Local-Assum"
     (wf Δ (Γ (x : t)))]

    [(wf Δ Γ)
     #;(type-check Δ Γ e t)
     #;(type-infer Δ Γ t U)
     ----------------------- "W-Local-Def"
     (wf Δ (Γ (x = e : t)))]

    [(wf Δ ·)
     (where #f (Δ-in-dom Δ D))
     (where ((c_i : t_i) ...) (Δ-ref-constructor-map Δ_0 D))
     (where (c_!_0 ...) (c_i ...)) ; all constructors unique
     (side-condition ,(eq? (term n) (length (term V))))
     (side-condition (full-types-only t)) ;; I5
     (type-infer Δ · t U_D) ;; I1
     (valid-constructor Δ_0 (c_i : t_i)) ...
     ;; Positivity conditions
     (where Ξ_p (Ξ-take-parameters Δ_0 D Ξ))
     (where Ξ_i (Ξ-take-indices    Δ_0 D Ξ))
     (where ((x : _) ...) (Ξ-flatten Ξ_p))
     (pos-context Δ_0 V (x ...) Ξ_i) ;; I8
     --------------------------------------------------------- "W-Ind"
     (wf (name Δ_0 (Δ (D : n V (name t (in-hole Ξ U)) _))) ·)])) ;; I3

(module+ test
  (redex-judgment-holds-chk
   valid-constructor
   [Δ01 (tt : IUnit)]
   [Δb (true : IBool)]
   [Δb (false : IBool)]
   [Δnb (z : INat)]
   [Δnb (s : (Π (x : INat) INat))]
   [Δlist (nil : (Π (A : Set) (I@ List A)))]
   [Δlist (cons : (-> (A : Set) (a : A) (ls : (I@ List A)) (I@ List A)))])

  (redex-relation-chk
   wf
   [· ·]
   [Δ0 ·]
   [Δ01 ·]
   [Δb ·]
   [Δnb ·]
   [Δnb (· (x : INat))]
   [Δlist ·]
   [#:f Δbadlist ·]
   [Δlist (· (x = (λ (x : INat) (λ (y : INat) y)) : (Π (x : INat) (Π (y : INat) INat))))]
   [Δlist ((· (x = (λ (x : INat) (λ (y : INat) y)) : (Π (x : INat) (Π (y : INat) INat))))
           (y = (λ (x : INat) (λ (y : INat) y)) : (Π (x : INat) (Π (y : INat) INat))))]
   [Δlist (· (x = subn : (Π (y : INat) INat)))]
   [Δnb (· (x = subn : (Π (y : INat) INat)))]
   ; This passes, but is very slow without a large cache.
   #;[Δnb ((· (x = subn : (Π (y : INat) INat)))
           (z = subn : (Π (y : INat) INat)))]))

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
     (side-condition (no-free-stage-vars e))
     ------------------------------------------------- "Lam"
     (type-infer Δ Γ (λ (x : t_0) e) (Π (x : t_0) t))]

    [(type-infer Δ Γ e_0 (Π (x : t_1) t))
     (type-check Δ Γ e_1 t_1)
     (side-condition (no-free-stage-vars e_1))
     -------------------------------------------------- "App"
     (type-infer Δ Γ (@ e_0 e_1) (substitute t x e_1))]

    [(type-check Δ Γ e t)
     (type-infer Δ (Γ (x = e : t)) e_body t_body)
     ------------------------------------------------------------------ "Let"
     (type-infer Δ Γ (let (x = e : t) e_body) (substitute t_body x e))]

    [(ind-type d D)
     (Δ-type-in Δ D t_D)
     (where D_0 (free-variable (Δ Γ) D))
     (where Θ (Θ-build (t_pa ...)))
     (type-infer Δ (Γ (D_0 : t_D)) (in-hole Θ D_0) t) ;; Treat inductive type as a normal function
     (simple Δ (I@ d t_pa ...))
     -------------------------------------------- "Ind"
     (type-infer Δ Γ (I@ d t_pa ...) t)]

    [(Δ-constr-in Δ c t_c) (wf Δ Γ)
     (where c_0 (free-variable (Δ Γ) c))
     (where s (free-variable (Δ Γ t_c c_0) ,'s))
     (where Θ_c (Θ-build (e_pa ...)))
     (type-infer Δ (Γ (c_0 : t_c)) (in-hole Θ_c c_0) (I@ d e ...)) ;; Treat constructor as a normal function
     (ind-type d D)
     (where t (I@ (D (^ s)) e ...)) ;; Inductive type returned must have a successor stage
     (simple Δ t)
     --------------------------------- "Constr"
     (type-infer Δ Γ (C@ c e_pa ...) t)]

    [(type-infer Δ Γ e (name t_I (I@ d e_pi ...)))
     (ind-type d D)
     (where Θ (Θ-build (e_pi ...)))
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
   [(λ (x : INat) INat) t]
   [(λ (x : INat) INat) t]
   [(case Cz (λ (x : INat) INat) (Cz (λ (x : INat) x))) t]
   [#:f nil (I@ List A)]
   [CnilNat t]
   [IListNat Set]
   [(C@ cons INat Cz CnilNat) t]
   [subn t]
   [plus t]
   [#:f subn-bad1 t]
   [#:f subn-bad2 t]
   [#:f Ω t])

  (redex-relation-chk
   type-check
   [· (· (Nat : (Type 0))) (Π (n : Nat) Nat) (Type 1)]
   [· (· (Nat : Set)) (Π (n : Nat) Nat) (Type 1)]
   [Δnb (· (x : INat)) INat Set]
   [Δnb (· (Nat : Set)) (λ (n : Nat) n) (Π (n : Nat) Nat)]
   [Δnb ((· (f : (-> INat INat))) (x : INat))
        (case x (λ (x : INat) INat)
              (Cz
               (λ (x : INat) (@ f x))))
        INat]
   [Δnb (· (f : (-> INat INat)))
    (λ (x : INat)
      (case x (λ (x : INat) INat)
            (Cz
             (λ (x : INat) (@ f x)))))
    (Π (y : INat) INat)])

  (redex-relation-chk
   (type-check Δlist ·)
   [INat Set]
   [Cz INat]
   [(C@ s Cz) INat]
   [(Π (x : INat) Set) (Type 1)]
   [(λ (x : INat) INat) (Π (x : INat) Set)]
   [(λ (x : INat) x) (Π (x : INat) INat)]
   [(case Cz (λ (x : INat) INat) (Cz (λ (x : INat) x))) INat]
   [(case Ctrue (λ (x : IBool) INat) (Cz (C@ s Cz))) INat]
   [(fix f : (-> INat INat)
         (λ (x : INat)
           (case x (λ (x : INat) INat)
                 (Cz
                  (λ (x : INat) (C@ s x))))))
    (Π (x : INat) INat)]
   [(fix f : (-> INat INat)
         (λ (x : INat)
           (case x (λ (x : INat) INat)
                 (Cz
                  (λ (x : INat) (@ f x))))))
    (Π (x : INat) INat)]
   [#:f (fix f : (-> INat INat)
             (λ (x : INat)
               (case x (λ (x : INat) INat)
                     ((@ f x)
                      (λ (y : INat) (@ f x))))))
    (Π (x : INat) INat)]
   [(let ([n = Cz : INat]) Cz) INat]
   [(let ([n = Cz : INat]) n) INat]
   [(let ([Nat^ = INat : Set] [n = Cz : Nat^]) n) INat]
   [(C@ cons INat Cz CnilNat) IListNat]
   [(case (C@ cons INat Cz CnilNat) (λ (ls : IListNat) IBool)
          (Ctrue (λ (n : INat) (ls : IListNat) Cfalse))) IBool]))

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

    [(ind-type d D)
     (where ((e_p ...) (e_i ...)) (take-parameters-indices Δ D (e ...)))
     (where (v ...) (Δ-ref-polarities Δ D))
     (pos-stage-polarity Δ v s e_p) ...
     (side-condition (not-free-in s (e_i ...)))
     ---------------------------------
     (pos-stage Δ s (I@ d e ...))])

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
     (where ((e_p ...) (e_i ...)) (take-parameters-indices Δ D (e ...)))
     (where (v ...) (Δ-ref-polarities Δ D))
     (neg-stage-polarity Δ v s e_p) ...
     (side-condition (not-free-in s (e_i ...)))
     ---------------------------------
     (neg-stage Δ s (I@ (D S) e ...))]

    [(neg-stage Δ s (I@ (D ∞) e ...))
     -----------------------------
     (neg-stage Δ s (I@ D e ...))])

  (define-judgment-form cicL
    #:mode (pos-stage-polarity I I I I)
    #:contract (pos-stage-polarity Δ v s e)

    [(pos-stage Δ s e)
     ------------------------------
     (pos-stage-polarity Δ ⊕ s e)]

    [(pos-stage Δ s e)
     -----------------------------
     (pos-stage-polarity Δ + s e)]

    [(neg-stage Δ s e)
     -----------------------------
     (pos-stage-polarity Δ - s e)]

    [(side-condition (not-free-in s e))
     -----------------------------
     (pos-stage-polarity Δ ○ s e)])

  (define-judgment-form cicL
    #:mode (neg-stage-polarity I I I I)
    #:contract (neg-stage-polarity Δ v s e)

    [(neg-stage Δ s e)
     ------------------------------
     (neg-stage-polarity Δ ⊕ s e)]

    [(neg-stage Δ s e)
     -----------------------------
     (neg-stage-polarity Δ + s e)]

    [(pos-stage Δ s e)
     -----------------------------
     (neg-stage-polarity Δ - s e)]

    [(side-condition (not-free-in s e))
     -----------------------------
     (neg-stage-polarity Δ ○ s e)]))

(module+ test
  (redex-judgment-holds-chk
   (pos-stage Δlist)
   [s Prop]
   [s (Π (x : Prop) Set)]
   [s (I@ (List s) (I@ (Nat s)))]
   [s (Π (n : Nat) (I@ (List s) INat))]))

(module+ test
  (redex-judgment-holds-chk
   (neg-stage Δlist)
   [s Prop]
   [s (Π (x : Prop) Set)]
   [s (I@ (List r) (I@ (Nat r)))]
   [s (Π (l : (I@ (List s) INat)) (I@ (Nat r)))]))

(module+ test
  (redex-judgment-holds-chk
   (pos-stage-polarity Δlist)
   [⊕ s (I@ (List s) INat)]
   [+ s (I@ (List s) INat)]
   [- s (I@ (List r) INat)]
   [○ s INat]))

(module+ test
  (redex-judgment-holds-chk
   (neg-stage-polarity Δlist)
   [⊕ s (I@ (List r) INat)]
   [+ s (I@ (List r) INat)]
   [- s (I@ (List s) INat)]
   [○ s INat]))

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
     ---------------------------------
     (pos-term Δ x (Π (x : t_0) t_1))]

    [(ind-type d D)
     (where ((e_p ...) (e_i ...)) (take-parameters-indices Δ D (e ...)))
     (where (v ...) (Δ-ref-polarities Δ D))
     (pos-term-polarity Δ v x e_p) ...
     (side-condition (all ((not-free-in x e_i) ...)))
     --------------------------------
     (pos-term Δ x (I@ d e ...))])

  (define-judgment-form cicL
    #:mode (neg-term I I I)
    #:contract (neg-term Δ x e)

    [(side-condition (not-free-in x e))
     ------------------
     (neg-term Δ x e)]

    [(pos-term Δ x t_0) (neg-term Δ x t_1)
     ---------------------------------
     (neg-term Δ x (Π (y : t_0) t_1))]

    [(ind-type d D)
     (where ((e_p ...) (e_i ...)) (take-parameters-indices Δ D (e ...)))
     (where (v ...) (Δ-ref-polarities Δ D))
     (neg-term-polarity Δ v x e_p) ...
     (side-condition (all ((not-free-in x e_i) ...)))
     --------------------------------
     (neg-term Δ x (I@ d e ...))])

  (define-judgment-form cicL
    #:mode (pos-term-polarity I I I I)
    #:contract (pos-term-polarity Δ v x e)

    [(pos-term Δ x e)
     -----------------------------
     (pos-term-polarity Δ ⊕ x e)]

    [(pos-term Δ x e)
     ----------------------------
     (pos-term-polarity Δ + x e)]

    [(neg-term Δ x e)
     ----------------------------
     (pos-term-polarity Δ - x e)]

    [(side-condition (not-free-in x e))
     ----------------------------
     (pos-term-polarity Δ ○ x e)])

  (define-judgment-form cicL
    #:mode (neg-term-polarity I I I I)
    #:contract (neg-term-polarity Δ v x e)

    [(neg-term Δ x e)
     -----------------------------
     (neg-term-polarity Δ ⊕ x e)]

    [(neg-term Δ x e)
     ----------------------------
     (neg-term-polarity Δ + x e)]

    [(pos-term Δ x e)
     ----------------------------
     (neg-term-polarity Δ - x e)]

    [(side-condition (not-free-in x e))
     ----------------------------
     (neg-term-polarity Δ ○ x e)]))

(module+ test
  (redex-judgment-holds-chk
   (pos-term Δlist)
   [x Prop]
   [x x]
   [x (Π (x : Prop) Set)]
   [x (Π (x : Set) (I@ List x))]))

(module+ test
  (redex-judgment-holds-chk
   (neg-term Δlist)
   [x Prop]
   [x (Π (x : Prop) Set)]
   [x (Π (y : (I@ List x)) INat)]))

(module+ test
  (redex-judgment-holds-chk
   (pos-term-polarity Δlist)
   [⊕ x (I@ List x)]
   [+ x (I@ List x)]
   [- x (Π (y : (I@ List x)) INat)]
   [○ x INat]))

(module+ test
  (redex-judgment-holds-chk
   (neg-term-polarity Δlist)
   [⊕ x (Π (y : (I@ List x)) INat)]
   [+ x (Π (y : (I@ List x)) INat)]
   [- x (I@ List x)]
   [○ x INat]))

(begin ;; positivity of contexts
  ;; I don't think we need rules for let-contexts (i.e. (Γ (x = e : t)))

  (define-judgment-form cicL
    #:mode (pos-context I I I I)
    #:contract (pos-context Δ V (x ...) Ξ)

    [-----------------------
     (pos-context Δ () () Ξ)]

    [(where ((_ : t) ...) (Ξ-flatten Ξ))
     (pos-term Δ x t) ...
     (pos-context Δ (v ...) (x_0 ...) Ξ)
     -----------------------------------------
     (pos-context Δ (⊕ v ...) (x x_0 ...) Ξ)]

    [(where ((_ : t) ...) (Ξ-flatten Ξ))
     (pos-term Δ x t) ...
     (pos-context Δ (v ...) (x_0 ...) Ξ)
     ----------------------------------------
     (pos-context Δ (+ v ...) (x x_0 ...) Ξ)]

    [(where ((_ : t) ...) (Ξ-flatten Ξ))
     (neg-term Δ x t) ...
     (pos-context Δ (v ...) (x_0 ...) Ξ)
     ----------------------------------------
     (pos-context Δ (- v ...) (x x_0 ...) Ξ)]

    [(where ((_ : t) ...) (Ξ-flatten Ξ))
     (side-condition (all ((not-free-in x t) ...)))
     (pos-context Δ (v ...) (x_0 ...) Ξ)
     ----------------------------------------
     (pos-context Δ (○ v ...) (x x_0 ...) Ξ)]))

(module+ test
 (redex-judgment-holds-chk
  (pos-context Δlist)
  [(⊕) (x) (Π (y : (Π (y : INat) (I@ List x))) hole)]
  [(+) (x) (Π (y : (Π (y : INat) (I@ List x))) hole)]
  [(-) (x) (Π (y : (Π (y : (I@ List x)) INat)) hole)]
  [(○) (x) (Π (y : INat) hole)]
  [(+ ○) (x y) (Π (y : (Π (z : INat) (I@ List x))) hole)]))

(begin ;; strict positivity

  (define-judgment-form cicL
    #:mode (strict-positivity I I I)
    #:contract (strict-positivity Δ D t)

    [(side-condition (not-free-in D t))
     --------------------------
     (strict-positivity Δ D t)]

    [(full-type d D)
     (side-condition (all ((not-free-in D e) ...)))
     -------------------------------------
     (strict-positivity Δ D (I@ d e ...))]

    [(side-condition (not-free-in D t_1))
     (strict-positivity Δ D t_2)
     ------------------------------------------
     (strict-positivity Δ D (Π (x : t_1) t_2))]

    [(full-type d D_0)
     (side-condition (Δ-in-dom Δ D_0))
     (where ((e_p ...) (e_i ...)) (take-parameters-indices Δ D_0 (e ...)))
     (where (v ...) (Δ-ref-polarities Δ D_0))
     (side-condition (all ((not-free-in D e_i) ...)))
     (strict-positivity-polarity Δ v D e_p) ...
     -------------------------------------
     (strict-positivity Δ D (I@ d e ...))]

    [(strict-positivity Δ D (I@ d))
     --------------------------
     (strict-positivity Δ D d)])

  (define-judgment-form cicL
    #:mode (strict-positivity-polarity I I I I)
    #:contract (strict-positivity-polarity Δ v D e)

    [(strict-positivity Δ D e)
     --------------------------------------
     (strict-positivity-polarity Δ ⊕ D e)]

    [(side-condition (not-free-in D e))
     -------------------------------------
     (strict-positivity-polarity Δ v D e)])

  (define-judgment-form cicL
    #:mode (strict-positivity-product I I I)
    #:contract (strict-positivity-product Δ x Ξ)

    [-------------------------------------
     (strict-positivity-product Δ x hole)]

    [(strict-positivity Δ x t)
     (strict-positivity-product Δ x Ξ)
     ----------------------------------------------
     (strict-positivity-product Δ x (Π (_ : t) Ξ))]))

(module+ test
  (redex-judgment-holds-chk
   (strict-positivity Δlist)
   [Nat Prop]
   [Nat (I@ (Nat ∞))]
   [List (I@ (List ∞) (I@ (Nat ∞)))]
   [Nat (Π (x : Set) (I@ (Nat ∞)))]
   [Nat (I@ (List ∞) (I@ (Nat ∞)))]))

(module+ test
  (redex-judgment-holds-chk
   (strict-positivity-polarity Δlist)
   [⊕ Nat (I@ (List ∞) (I@ (Nat ∞)))]
   [+ List (I@ (Nat ∞))]
   [- List (I@ (Nat ∞))]
   [○ List (I@ (Nat ∞))]))

(begin ;; simple types

  (define-judgment-form cicL
    #:mode (simple I I)
    #:contract (simple Δ t)

    [(side-condition (no-free-stage-vars t))
     ------------- "s-empty"
     (simple Δ t)]

    [(simple Δ t_1) (simple Δ t_2)
     ----------------------------- "s-prod"
     (simple Δ (Π (x : t_1) t_2))]

    [(ind-type d D)
     (side-condition (Δ-in-dom Δ D))
     (where ((e_p ...) (e_i ...)) (take-parameters-indices Δ D (e ...)))
     (where (v ...) (Δ-ref-polarities Δ D))
     (side-condition (all ((no-free-stage-vars e_i) ...)))
     (simple-polarity Δ v e_p) ...
     ------------------------ "s-ind"
     (simple Δ (I@ d e ...))])

  (define-judgment-form cicL
    #:mode (simple-polarity I I I)
    #:contract (simple-polarity Δ v e)

    [(side-condition (no-free-stage-vars t))
     ------------------------ "sv-inv"
     (simple-polarity Δ ○ t)]

    [(simple Δ t)
     ------------------------ "sv-ninv"
     (simple-polarity Δ v t)]))

(module+ test
  (redex-judgment-holds-chk
   (simple Δlist)
   [(Π (x : (I@ (List s) (I@ (Nat s)))) (Π (y : (I@ (Nat ∞))) (Π (z : (I@ (List ∞) (I@ (Nat s))))  (I@ (Nat ∞)))))]))

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

    [(where ((c : (in-hole Ξ (I@ d e ...)))) (Δ-ref-constructor-map Δ D))
     (where ((_ : Prop) ...) (Ξ-flatten Ξ))
     (ind-type d D)
     ---------------------- "Prop-extended-singleton"
     (elimable Δ D Prop U)])

  (define-judgment-form cicL
    #:mode (check-motive I I I I I I)
    #:contract (check-motive Δ Γ t D Θ e)

    [(where Ξ_D (Δ-ref-index-Ξ Δ D Θ_p))
     (where (e_p ...) (Θ-flatten Θ_p))
     (where ((x_i : _) ...) (Ξ-flatten Ξ_D))
     ;; check that the motive matches the inductive index telescope, i.e., the telescope sans parameters.
     ;; TODO: Check subtyping between Ξ_D, rather than α-equiv?
     (type-infer Δ Γ e (in-hole Ξ_D (Π (x : t_D) U_B)))
     (subtype Δ Γ t_D (I@ (D ∞) e_p ... x_i ...))
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

    [(guard Δ y D f any e) ...
     ---------------------------------
     (guard Δ y D f any (C@ c e ...))]

    [(guard Δ y D f any e) ...
     ---------------------------------
     (guard Δ y D f any (I@ d e ...))]

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

    [(ind-type d D) (Δ-type-in Δ D _)
     (guard Δ y D f () e)
     -------------------------------------------------------------------------------
     (terminates Δ (fix f : (Π (x : (I@ d e_j ...)) t) (λ (y : (I@ d e_j ...)) e)))]))

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
    [(no-free-stage-vars (I@ (D ∞) e ...))
     (all ((no-free-stage-vars e) ...))]
    [(no-free-stage-vars (I@ (D S) e ...))
     #f
     (where s (base S))]
    [(no-free-stage-vars (I@ d e ...))
     (all ((no-free-stage-vars e) ...))]
    [(no-free-stage-vars (C@ c e ...))
     (all ((no-free-stage-vars e) ...))]
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
           (term (all ((no-free-stage-vars e) ...))))]
    [(no-free-stage-vars (fix f : t e))
     ,(and (term (no-free-stage-vars t))
           (term (no-free-stage-vars e)))]
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
    [(full-types-only (I@ D e ...))
     (all ((full-types-only e) ...))]
    [(full-types-only (I@ (D ∞) e ...))
     (all ((full-types-only e) ...))]
    [(full-types-only (I@ d e ...)) #f]
    [(full-types-only (C@ c e ...))
     (all ((full-types-only e) ...))]
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
           (term (all ((full-types-only e) ...))))]
    [(full-types-only (fix f : t e))
     ,(and (term (full-types-only t))
           (term (full-types-only e)))]
    [(full-types-only    _ ) #t])

  (define-judgment-form cicL
    #:mode (full-type I O)
    #:contract (full-type d D)

    [----------------
     (full-type D D)]

    [--------------------
     (full-type (D ∞) D)])

  (define-judgment-form cicL
    #:mode (ind-type I O)
    #:contract (ind-type d D)

    [---------------
     (ind-type D D)]

    [-------------------
     (ind-type (D _) D)])

  (define-judgment-form cicL
    #:mode (annot-type I O)
    #:contract (annot-type d (D S))

    [-------------------------
     (annot-type (D S) (D S))]

    [---------------------
     (annot-type D (D ∞))]))

(begin ;; V defs
  ;; Get parameter variables where polarity is noninvariant (strictly positive, positive, or negative)
  (define-metafunction cicL
    pos-neg-variables : V Ξ -> (x ...)
    [(pos-neg-variables () hole) ()]

    [(pos-neg-variables (○ v ...) (Π (_ : _) Ξ))
     (pos-neg-variables (v ...) Ξ)]

    [(pos-neg-variables (⊕ v ...) (Π (_ : _) Ξ))
     (pos-neg-variables (v ...) Ξ)]

    [(pos-neg-variables (v_0 v ...) (Π (x_0 : _) Ξ))
     (x_0 x ...)
     (where (x ...) (pos-neg-variables (v ...) Ξ))])

  ;; Get parameter variables where polarity is strictly positive
  (define-metafunction cicL
    strictly-positive-variables : V Ξ -> (x ...)
    [(strictly-positive-variables () hole) ()]

    [(strictly-positive-variables (⊕ v ...) (Π (x_0 : _) Ξ))
     (x_0 x ...)
     (where (x ...) (strictly-positive-variables (v ...) Ξ))]

    [(strictly-positive-variables (v_0 v ...) (Π (_ : _) Ξ))
     (strictly-positive-variables (v ...) Ξ)]))

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
     (Δ-type-in Δ D t)])

  ;; Return the number of parameters for the inductive type D
  (define-metafunction cicL
    Δ-ref-parameter-count : Δ_0 D_0 -> n
    #:pre (Δ-in-dom Δ_0 D_0)
    [(Δ-ref-parameter-count Δ D)
     n
     (where (D : n _ _ _) (snoc-env-ref Δ D))])

  ;; Return the number of non-parameter arguments (indices) for the inductive type D
  (define-metafunction cicL
    Δ-ref-non-parameter-count : Δ_0 D_0 -> n
    #:pre (Δ-in-dom Δ_0 D_0)
    [(Δ-ref-non-parameter-count Δ D)
     ,(- (term (Ξ-length Ξ)) (term n))
     (where n (Δ-ref-parameter-count Δ D))
     (judgment-holds (Δ-type-in Δ D (in-hole Ξ (in-hole Θ U))))])

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
     (judgment-holds (Δ-constr-in Δ c (in-hole Ξ (I@ d e ...))))])

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
     (where (in-hole Ξ (I@ d e ...)) (instantiate t Θ))])

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
     (where n (Δ-ref-parameter-count Δ D))])

  (define-metafunction cicL
    Ξ-take-indices : Δ c Ξ -> Ξ
    [(Ξ-take-indices Δ c Ξ)
     (Ξ-drop Ξ n)
     (judgment-holds (Δ-constr-in Δ c t))
     (where n (Δ-constructor-ref-parameter-count Δ c))]
    [(Ξ-take-indices Δ D Ξ)
     (Ξ-drop Ξ n)
     (where #t (Δ-in-dom Δ D))
     (where n (Δ-ref-parameter-count Δ D))])

  (define-metafunction cicL
    Ξ-take-parameters : Δ c Ξ -> Ξ
    [(Ξ-take-parameters Δ c Ξ)
     (Ξ-take Ξ n)
     (judgment-holds (Δ-constr-in Δ c t))
     (where n (Δ-constructor-ref-parameter-count Δ c))]
    [(Ξ-take-parameters Δ D Ξ)
     (Ξ-take Ξ n)
     (where #t (Δ-in-dom Δ D))
     (where n (Δ-ref-parameter-count Δ D))])

  (define-metafunction cicL
    take-parameters-indices : Δ D (e ...) -> ((e ...) (e ...))
    [(take-parameters-indices Δ D (e ...))
     ((e_p ...) (e_i ...))
     (where #t (Δ-in-dom Δ D))
     (where n (Δ-ref-parameter-count Δ D))
     (where (e_p ...) (take (e ...) n))
     (where (e_i ...) (drop (e ...) n))]
    [(take-parameters-indices Δ c (e ...))
     ((e_p ...) (e_i ...))
     (judgment-holds (Δ-constr-in Δ c t))
     (where n (Δ-constructor-ref-parameter-count Δ c))
     (where (e_p ...) (take (e ...) n))
     (where (e_i ...) (drop (e ...) n))]))

(begin ;; aux defs
  (define-metafunction cicL
    I@-to-@ : D t -> t
    [(I@-to-@ D (I@ d e_I ...))
     (in-hole (Θ-build (e ...)) d)
     (where (e ...) ((I@-to-@ D e_I) ...))
     (judgment-holds (ind-type d D))]
    [(I@-to-@ D (Π (x : t_I0) t_I1))
     (Π (x : t_0) t_1)
     (where t_0 (I@-to-@ D t_I0))
     (where t_1 (I@-to-@ D t_I1))]
    [(I@-to-@ D e) e])

  (define-metafunction cicL
    free-variable : (any ...) x -> x
    [(free-variable (any) x)
     ,(variable-not-in (term any) (term x))]
    [(free-variable (any any_0 ...) x)
     ,(variable-not-in (term any) (term x_0))
     (where x_0 (free-variable (any_0 ...) x))])

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

  (define-metafunction cicL
    Θ-build : (e ...) -> Θ
    [(Θ-build ())
     hole]
    [(Θ-build (e e_r ...))
     (in-hole (Θ-build (e_r ...)) (@ hole e))])

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

  (define-metafunction cicL
    drop : (e_0 ...) n_0 -> (e ...)
    #:pre ,(<= (term n_0) (length (term (e_0 ...))))
    [(drop (e ...) 0)
     (e ...)]
    [(drop (e_0 e ...) n)
     (drop (e ...) ,(sub1 (term n)))])

  (define-metafunction cicL
    take : (e_0 ...) n_0 -> (e ...)
    #:pre ,(<= (term n_0) (length (term (e_0 ...))))
    [(take (e ...) 0)
     ()]
    [(take (e_0 e ...) n)
     (e_0 e_r ...)
     (where (e_r ...) (take (e ...) ,(sub1 (term n))))])

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
   (Δ-ref-constructor-type Δnb z) INat
   (Δ-ref-constructor-type Δnb s) (Π (x : INat) INat)
   (Δ-ref-index-Ξ Δnb Nat hole) hole
   (Δ-ref-constructor-map Δnb Nat) ((z : INat) (s : (Π (x : INat) INat)))

   #:m hole (Δ-constructor-ref-index-Ξ Δnb z hole)
   #:m (Π (x : (I@ Nat)) hole) (Δ-constructor-ref-index-Ξ Δnb s hole)
   #:m hole (Δ-constructor-ref-index-Ξ Δlist nil (@ hole INat))

   #:m (Π (x_2 : (I@ Nat)) (Π (x_3 : (I@ List (I@ Nat))) hole)) (Δ-constructor-ref-index-Ξ Δlist cons (@ hole (I@ Nat)))
   (Ξ-apply hole Nat) Nat
   (in-hole hole (Π (x : (Ξ-apply hole INat)) Set)) (Π (x : INat) Set)
   (Δ-key-by-constructor Δnb z) Nat))
