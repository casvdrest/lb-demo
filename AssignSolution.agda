module Assign where

open import Agda.Builtin.String
open import Agda.Builtin.Nat

{- =============================================================================

   Prelude

   Some types/functions needed for the formalization. Normally, you'd find these
   in Agda's standard library. 

   ============================================================================= -}


-- Sum/Either
data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B 

data Bool : Set where
  true false : Bool 

_&&_ : Bool → Bool → Bool
true  && b = b
false && b = false

!_ : Bool → Bool
! true = false
! false = true

-- Dependent product (Sigma) type 
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst 

open Σ

-- Non dependent products 
_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B 

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

_++_ : ∀ {A} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- The 'All' relation asserts that all elements of a list satisfy a given predicate 'P' 
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs) 

-- Empty type (bottom) 
data ⊥ : Set where

-- From the empty type we can derive anything 
absurd : ∀ {A : Set} → ⊥ → A 
absurd ()

-- Equality 
data _≡_ {a} {A : Set a} (x : A) : A → Set where
  refl : x ≡ x

¬ : Set → Set
¬ P = P → ⊥ 


{- =============================================================================

   Expressions

   ============================================================================= -} 

Name = String 

-- Expr ∷= Identifier | ℕ | 𝔹
--       | Expr '+' Expr | Expr '*' Expr
--       | Expr '&&' Expr | Expr '||' Expr
--       | '!' Expr
-- 
data Expr : Set where
  var    : Name → Expr
  nlit   : Nat → Expr
  blit   : Bool → Expr
  add    : Expr → Expr → Expr
  and    : Expr → Expr → Expr
  not    : Expr → Expr  

data Type : Set where
  tnum  : Type
  tbool : Type

Ctx  = List (Name × Type)


-- Context membership.

-- A value of type 'x ↦ t ∈ Γ' proves that 'Γ' contains the pair '(x , t)'
-- somewhere. This is a *proof relevant* relation: by pattern matching on the
-- proof we learn where in 'Γ' we can find it.
data _↦_∈_ {A} : Name → A → List (Name × A) → Set where

  here  : ∀ {Γ x v}
            -------------------
          → x ↦ v ∈ ((x , v) ∷ Γ) 

  there : ∀ {Γ x y s t}
          → x ↦ t ∈ Γ
          → ¬ (x ≡ y)
            ---------------------
          → x ↦ t ∈ ((y , s) ∷ Γ)


-- Expression typing.
--
-- A value of type 'Γ ⊢ e ⦂ t' proves that 'e' is well-typed with type 't' under
-- context 'Γ'. The constructors of this data type match with the typing rules
-- of expressions in the assign language.
data _⊢_⦂_ (Γ : Ctx) : Expr → Type → Set where

  [E-var]  : ∀ {x t}
             → x ↦ t ∈ Γ
               -------------
             → Γ ⊢ var x ⦂ t  
    
  [E-nlit] : ∀ {n}
               -----------------
             → Γ ⊢ nlit n ⦂ tnum

  [E-blit] : ∀ {b}
               ------------------
             → Γ ⊢ blit b ⦂ tbool

  [E-add]  : ∀ {e₁ e₂}
             → Γ ⊢ e₁ ⦂ tnum
             → Γ ⊢ e₂ ⦂ tnum
               --------------------
             → Γ ⊢ add e₁ e₂ ⦂ tnum 

  [E-and]  : ∀ {e₁ e₂}
             → Γ ⊢ e₁ ⦂ tbool
             → Γ ⊢ e₂ ⦂ tbool
               ---------------------
             → Γ ⊢ and e₁ e₂ ⦂ tbool 

  [E-not]  : ∀ {e}
             → Γ ⊢ e ⦂ tbool
               -----------------
             → Γ ⊢ not e ⦂ tbool

-- Heap
--
-- A heap is indexed by a context 'Γ', to enforce that it contains entries for
-- the same name in the same order. By doing this we can relate entries in the
-- static context 'Γ' to a location on the heap, which will be necessary later
-- when proving the preservation lemma for expressions. 
data Heap : Ctx → Set where
  empty  : Heap []
  
  extend : ∀ {Γ t}
           → (x : Name)
           → Expr 
           → Heap Γ
             ------------------
           → Heap ((x , t) ∷ Γ)


-- Heap membership
--
-- A value of type 'get⟨ h , x ⟩= e' proves that the name 'x' maps to the
-- expression 'e' in heap 'h'. Again, this is a *proof relevant* relation: we
-- can find out *where* in 'h' we can find the key 'x' by pattern matching on
-- the proof.
data get⟨_,_⟩=_ : ∀ {Γ} → Heap Γ → Name → Expr → Set where

  hereʰ : ∀ {Γ t x} {h : Heap Γ} {e : Expr}
          ------------------------------------
        → get⟨ extend {t = t} x e h , x ⟩= e

  thereʰ : ∀ {Γ x y t} {h : Heap Γ} {e e′ : Expr}
         → get⟨ h , x ⟩= e
         → ¬ (x ≡ y) 
           ----------------------------------------
         → get⟨ extend {t = t} y e′ h , x ⟩= e 


-- Heap well typedness. A proof of the form '⊢-Heap Γ′ h' proves that all
-- expressions stored in 'h' are well typed under context 'Γ′'. We can match on
-- the proof to get out derivations for the individual locations.
data ⊢-Heap (Γ′ : Ctx) : ∀ {Γ} → Heap Γ → Set where

  ⊢-empty  : ------------
             ⊢-Heap Γ′ empty
  
  ⊢-extend : ∀ {Γ e t x} {h : Heap Γ}
             → ⊢-Heap Γ′ h
             → Γ′ ⊢ e ⦂ t
               -----------------------------
             → ⊢-Heap Γ′ (extend {t = t} x e h)  

data _,_─→_ {Γ} (h : Heap Γ) : Expr → Expr → Set where

  ─→-var : ∀ {x e}
           → get⟨ h , x ⟩= e  
             ----------------
           → h , var x ─→ e  

  ─→-add₁ : ∀ {e₁ e₁′ e₂} 
            → h , e₁ ─→ e₁′
              ---------------------------
            → h , add e₁ e₂ ─→ add e₁′ e₂ 
            
  ─→-add₂ : ∀ {n e e′} 
            → h , e ─→ e′
              -------------------------------------
            → h , add (nlit n) e ─→ add (nlit n) e′ 
            
  ─→-add  : ∀ {n m} 
              -----------------------------------------
            → h , add (nlit n) (nlit m) ─→ nlit (n + m) 


  ─→-and₁ : ∀ {e₁ e₁′ e₂} 
            → h , e₁ ─→ e₁′
              ---------------------------
            → h , and e₁ e₂ ─→ and e₁′ e₂ 
            
  ─→-and₂ : ∀ {b e e′} 
            → h , e ─→ e′
              -------------------------------------
            → h , and (blit b) e ─→ and (blit b) e′ 
            
  ─→-and  : ∀ {b₁ b₂} 
              ----------------------------------------------
            → h , and (blit b₁) (blit b₂) ─→ blit (b₁ && b₂)


  ─→-not₁ : ∀ {e e′}
            → h , e ─→ e′ 
              -------------------
            → h , not e ─→ not e′

  ─→-not  : ∀ {b}
              ------------------------------
            → h , not (blit b) ─→ blit (! b) 

-- Preservation (Expressions):
--
-- If an expression 'e' is well-typed, all expressions stored on the heap are
-- well-typed, and 'e' reduces to 'e′', then 'e′' is also well-typed, under the
-- same context with the same type.

-- To prove preservation, we require one additional lemma stating that if a name
-- 'x' maps to a type 't' in some 'Γ', retrieving 'x' from the heap 'h' yields
-- the expression 'x', and all expressions stored on the heap are well-typed,
-- then 'e' has type 't'.
∈-to-⊢ : ∀ {Γ Γ′ t x e} {h : Heap Γ}
         → x ↦ t ∈ Γ
         → get⟨ h , x ⟩= e
         → ⊢-Heap Γ′ h
           ---------------
         → Γ′ ⊢ e ⦂ t
∈-to-⊢ here hereʰ (⊢-extend _ d) = d
∈-to-⊢ here (thereʰ x∈h ns) wth = absurd (ns refl)
∈-to-⊢ (there x∈Γ ns) hereʰ wth = absurd (ns refl)
∈-to-⊢ (there x∈Γ _) (thereʰ x∈h _) (⊢-extend wth x)
  = ∈-to-⊢ x∈Γ x∈h wth

-- Now we're ready to prove the main preservation lemma
E-preservation : ∀ {Γ t e e′} {h : Heap Γ}  
                 → Γ ⊢ e ⦂ t
                 → ⊢-Heap Γ h 
                 → h , e ─→ e′
                   -----------
                 → Γ ⊢ e′ ⦂ t

-- 'e' is a variable
E-preservation ([E-var] x∈Γ) hwt (─→-var x∈h)
  = ∈-to-⊢ x∈Γ x∈h hwt  

-- 'e' is an addition 
E-preservation ([E-add] d d₁) hwt (─→-add₁ st)
  = [E-add] (E-preservation d hwt st) d₁
E-preservation ([E-add] d d₁) hwt (─→-add₂ st)
  = [E-add] d (E-preservation d₁ hwt st)
E-preservation ([E-add] d d₁) hwt ─→-add
  = [E-nlit]

-- 'e' is a conjunction 
E-preservation ([E-and] d d₁) hwt (─→-and₁ st)
  = [E-and] (E-preservation d hwt st) d₁
E-preservation ([E-and] d d₁) hwt (─→-and₂ st)
  = [E-and] d (E-preservation d₁ hwt st)
E-preservation ([E-and] d d₁) hwt ─→-and
  = [E-blit]

-- 'e' is a negation 
E-preservation ([E-not] d) hwt (─→-not₁ st)
  = [E-not] (E-preservation d hwt st)
E-preservation ([E-not] d) hwt ─→-not
  = [E-blit]


--  Progress 
--
--  If an expression 'e' is well-typed, then it is either a literal, or there
--  exists some expression 'e′' such that 'e' reduces to 'e′'

-- Again, we'll need one additional lemma, in this case stating that if 'Γ'
-- contains an entry with key 'x', then a "Γ-shaped" heap must store an
-- expression for that key.
heap-lemma : ∀ {Γ t x} {h : Heap Γ}
             → x ↦ t ∈ Γ
               ---------------------------------
             → Σ Expr λ e → get⟨ h , x ⟩= e
heap-lemma {h = extend _ e _} here           =
  e , hereʰ
heap-lemma {h = extend _ _ h} (there x∈h ns)
  with heap-lemma {h = h} x∈h
... | e , p = e , thereʰ p ns

-- Furthermore, we use the following relation, where a value of type 'Literal e'
-- proves that 'e' is either a boolean or a number literal.
data Literal : Expr → Set where
  isNum  : ∀ {n} → Literal (nlit n)
  isBool : ∀ {b} → Literal (blit b) 


-- Progress lemma for expressions 
E-progress : ∀ {Γ t e} {h : Heap Γ}
             → Γ ⊢ e ⦂ t
               ----------------------------------------------
             → Either (Σ Expr λ e′ → h , e ─→ e′) (Literal e) 

-- 'e' is a variable 
E-progress ([E-var] x)
  = left (_ , ─→-var (heap-lemma x .snd))

-- 'e' is a number literal 
E-progress [E-nlit]
  = right isNum

-- 'e' is a Boolean literal 
E-progress [E-blit]
  = right isBool

-- 'e' is an addition 
E-progress ([E-add] d₁ d₂)
  with E-progress d₁
... | left  st = left (_ , ─→-add₁ (st .snd))
... | right isNum
  with E-progress d₂
... | left  st    = left (_ , ─→-add₂ (st .snd))
... | right isNum = left (_ , ─→-add)

-- 'e' is a negation 
E-progress ([E-and] d₁ d₂)
  with E-progress d₁
... | left st = left (_ , ─→-and₁ (st .snd))
... | right isBool
  with E-progress d₂ 
... | left  st     = left (_ , ─→-and₂ (st .snd))
... | right isBool = left (_ , ─→-and)

-- 'e' 
E-progress ([E-not] d)
  with E-progress d
... | left  st     = left (_ , ─→-not₁ (st .snd))
... | right isBool = left (_ , ─→-not)


-- Soundness for expressions follows from the lemmas 'E-preservation' and
-- 'E-progress'.
--
-- Progress tells us that well-typed expressions are either a literal, or they
-- can be reduced.  Preservation tells us that the reduced expression is also
-- well-typed (with the same type).
--
-- Hence, we conclude that for every well-typed expression there exists a
-- "chain" of reductions that turns it into a literal value of the right type.
--
-- Q: can we prove this statement in Agda? 



{- ============================================================================= 

   Statements/Programs 

   ============================================================================= -} 


-- Statements can be a:
-- * variable assignment
-- * if statement
-- * while statement
--
-- A program is simply a list of statements. We define programs and statements
-- mutually, because the branches in if and while statements can again be a list
-- of statements
mutual 
  data Stmt : Set where
    assign  : Name → Expr → Stmt
    if      : Expr → Prog → Prog → Stmt
    while   : Expr → Prog → Stmt 

  Prog = List Stmt



-- Statement/program typing
--
-- Again, we have to define these mutually. A judgment of the form Γ ⊢ s ↝ Γ′
-- asserts that a statement 's' is well-formed under context 'Γ', with 'Γ′'
-- describing the context after execution of the statement.
--
-- Currently, assignments always add a new variable to the context that shadows
-- any existing bindings, meaning that we can only a assign to avariables when
-- they are declared. How can we change the definitions of statements/programs
-- and/or their typing to allow assignment to existing variables?
mutual 
  data _⊢_↝_ (Γ : Ctx) : (s : Stmt) → (Γ′ : Ctx) → Set where


    [S-assign]  : ∀ {x e t}
                  → Γ ⊢ e ⦂ t
                    ------------------------------
                  → Γ ⊢ assign x e ↝ ((x , t) ∷ Γ) 


    [S-if]      : ∀ {e P₁ P₂} 
                  → Γ ⊢ e ⦂ tbool
                  → Γ ⊢ᵖ P₁ ↝ Γ
                  → Γ ⊢ᵖ P₂ ↝ Γ
                    ------------------
                  → Γ ⊢ if e P₁ P₂ ↝ Γ

    [S-while]   : ∀ {e P}
                  → Γ ⊢ e ⦂ tbool
                  → Γ ⊢ᵖ P ↝ Γ
                    -----------------
                  → Γ ⊢ while e P ↝ Γ
 

  data _⊢ᵖ_↝_ (Γ : Ctx) : Prog → Ctx → Set where

    [P-empty] :   ------
                  Γ ⊢ᵖ [] ↝ Γ 
    
    [P-cons]  : ∀ {Γ′ Γ′′ s P}
                → Γ ⊢ s ↝ Γ′  
                → Γ′ ⊢ᵖ P ↝ Γ′′
                  ----------------
                → Γ ⊢ᵖ s ∷ P ↝ Γ′′

-- Transitivity of program well-formedness 
⊢ᵖ-trans : ∀ {Γ Γ′ Γ′′ P₁ P₂}
           → Γ  ⊢ᵖ P₁       ↝ Γ′
           → Γ′ ⊢ᵖ P₂       ↝ Γ′′
             -------------------
           → Γ  ⊢ᵖ P₁ ++ P₂ ↝ Γ′′ 
⊢ᵖ-trans [P-empty]       d₂ = d₂
⊢ᵖ-trans ([P-cons] d d₁) d₂ = [P-cons] d (⊢ᵖ-trans d₁ d₂)

-- auxiliary function that maps literals to their type 
typeOf : ∀ {e} → Literal e → Type
typeOf isNum  = tnum
typeOf isBool = tbool


-- Program reduction
--
-- A value of type 'h , P ─→ h′ , P′' proves that program 'P' reduces to 'P′',
-- with 'h' and 'h′' denoting the state of the heap before and after the
-- reduction.
data _,_─→_,_ {Γ} (h : Heap Γ) : ∀ {Γ′} → Prog → Heap Γ′ → Prog → Set where
                                                                      
  ─→-assign₁ : ∀ {P e e′ x}
               → h , e ─→ e′
                 -------------------------------------------
               → h , assign x e ∷ P ─→ h , (assign x e′ ∷ P)

  ─→-assign   : ∀ {P e x}
                → (l : Literal e)
                  -----------------------------------------------------
                → h , assign x e ∷ P ─→ extend {t = typeOf l} x e h , P 

  ─→-if₁      : ∀ {e e′ P₁ P₂ P}
                → h , e ─→ e′
                  -------------------------------------------
                → h , if e P₁ P₂ ∷ P ─→ h , (if e′ P₁ P₂ ∷ P)

  ─→-if-true  : ∀ {P₁ P₂ P}
                  ---------------------------------------------
                → h , if (blit true) P₁ P₂ ∷ P ─→ h , (P₁ ++ P)

  ─→-if-false : ∀ {P₁ P₂ P}
                  ----------------------------------------------
                → h , if (blit false) P₁ P₂ ∷ P ─→ h , (P₂ ++ P)


  ─→-while    : ∀ {e P₁ P}
                  -----------------------------------------------------------------
                → h , while e P₁ ∷ P ─→ h , (if e (P₁ ++ (while e P₁ ∷ [])) [] ∷ P) 

-- Preservation lemma for programs 
preservation : ∀ {Γ Γ′ Γ′′ P P′ }
                 {h : Heap Γ}
                 {h′ : Heap Γ′}
               → Γ ⊢ᵖ P ↝ Γ′′
               → ⊢-Heap Γ h 
               → h , P ─→ h′ , P′
                 ----------------
               → Γ′ ⊢ᵖ P′ ↝ Γ′′


-- Assignment
preservation ([P-cons] ([S-assign] x) d) hwt (─→-assign₁ st)
  with E-preservation x hwt st
... | r = [P-cons] ([S-assign] r) d
preservation ([P-cons] ([S-assign] [E-nlit]) d) hwt (─→-assign isNum)
  = d
preservation ([P-cons] ([S-assign] [E-blit]) d) hwt (─→-assign isBool)
  = d

-- If statements
preservation ([P-cons] ([S-if] d₁ d₂ d₃) d) hwt (─→-if₁ st)
  = [P-cons] ([S-if] (E-preservation d₁ hwt st) d₂ d₃) d
preservation ([P-cons] ([S-if] [E-blit] d₂ d₃) d) hwt ─→-if-true = ⊢ᵖ-trans d₂ d
preservation ([P-cons] ([S-if] [E-blit] d₂ d₃) d) hwt ─→-if-false = ⊢ᵖ-trans d₃ d

-- While statements 
preservation ([P-cons] d'@([S-while] d₁ d₂) d)    hwt ─→-while
  = ⊢ᵖ-trans ([P-cons] ([S-if] d₁ (⊢ᵖ-trans d₂ ([P-cons] d' [P-empty])) [P-empty]) [P-empty]) d

-- A predicate that asserts that a program is an empty list of statements
data Empty : Prog → Set where
  isEmpty : Empty [] 


-- Progress lemma for programs 
progress : ∀ {Γ Γ′′ P}
             {h : Heap Γ}
           → Γ ⊢ᵖ P ↝ Γ′′
             ------------------------------------------------------------------------------
           → Either (Σ (Prog × Σ Ctx Heap) λ (P′ , (Γ′ , h′)) → h , P ─→ h′ , P′) (Empty P)

-- Assignment 
progress [P-empty]
  = right isEmpty
progress ([P-cons] ([S-assign] d) _)
  with E-progress d
... | left (_ , st)
  = left (_ , (─→-assign₁ st))
... | right l
  = left (_ , (─→-assign l))

-- If statements
progress ([P-cons] ([S-if] d₁ d₂ d₃) d)
  with E-progress d₁ 
... | left  (_ , st)         = left (_ , ─→-if₁ st)
... | right (isBool {true})  = left (_ , ─→-if-true)
... | right (isBool {false}) = left (_ , ─→-if-false)

-- While statements 
progress ([P-cons] ([S-while] d₁ d₂) d)
  = left (_ , ─→-while)
