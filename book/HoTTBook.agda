{-# OPTIONS --without-K #-}

module book.HoTTBook where

open import HoTT public

-- Lemma 2.1.1 (path inverses)

book-2-1-1 : ∀ {i} {A : Type i} {x y : A} → (x == y) → (y == x)
book-2-1-1 = !

-- Lemma 2.1.2 (path composition)

book-2-1-2 : ∀ {i} {A : Type i} {x y z : A} → (x == y) → (y == z) → (x == z)
book-2-1-2 = _∙_

-- Lemma 2.1.4 (properties of path composition)

book-2-1-4-i : ∀ {i} {A : Type i} {x y : A} (p : x == y) → p == p ∙ idp
book-2-1-4-i = ! ∘ ∙-unit-r

book-2-1-4-i' : ∀ {i} {A : Type i} {x y : A} (p : x == y) → p == idp ∙ p
book-2-1-4-i' p = idp

book-2-1-4-ii : ∀ {i} {A : Type i} {x y : A} (p : x == y) → (! p) ∙ p == idp
book-2-1-4-ii = !-inv-l

book-2-1-4-ii' : ∀ {i} {A : Type i} {x y : A} (p : x == y) → p ∙ (! p) == idp
book-2-1-4-ii' = !-inv-r

book-2-1-4-iii : ∀ {i} {A : Type i} {x y : A} (p : x == y) → ! (! p) == p
book-2-1-4-iii = !-!

book-2-1-4-iv : ∀ {i} {A : Type i} {x y z w : A} (p : x == y) (q : y == z) (r : z == w)
  → p ∙ (q ∙ r) == (p ∙ q) ∙ r
book-2-1-4-iv p q r = ! (∙-assoc p q r)

-- Theorem 2.1.6 (Eckmann-Hilton):

book-2-1-6 : ∀ {i} {A : Ptd i} (α β : Ω^ 2 A) → α ∙ β == β ∙ α
book-2-1-6 = conc^2-comm

-- Definition 2.1.7 (pointed types)

book-2-1-7 : ∀ i → Type (lsucc i)
book-2-1-7 = Ptd

-- Definition 2.1.8 (loop spaces of pointed types)

book-2-1-8-i : ∀ {i} → Ptd i → Type i
book-2-1-8-i = Ω

book-2-1-8-ii : ∀ {i} → ℕ → Ptd i → Type i
book-2-1-8-ii = Ω^

-- Lemma 2.2.1 (ap)

book-2-2-1 : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A}
  → (x == y → f x == f y)
book-2-2-1 = ap

book-2-2-1' : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x : A}
  → ap f (idp {a = x}) == idp {a = f x}
book-2-2-1' f = idp

-- Lemma 2.2.2 (properties of ap)

book-2-2-2-i : ∀ {i} {A : Type i} {j} {B : Type j} (f : A → B) {x y z : A}
  → (p : x == y) → (q : y == z) → ap f (p ∙ q) == ap f p ∙ ap f q
book-2-2-2-i = ap-∙

book-2-2-2-ii : ∀ {i} {A : Type i} {j} {B : Type j} (f : A → B) {x y : A}
  → (p : x == y) → ap f (! p) == ! (ap f p)
book-2-2-2-ii = ap-!

book-2-2-2-iii : ∀ {i} {A : Type i} {j k} {B : Type j} {C : Type k}
  (g : B → C) (f : A → B) {x y : A}
  → (p : x == y) → ap (g ∘ f) p == ap g (ap f p)
book-2-2-2-iii = ap-∘

book-2-2-2-iv : ∀ {i} {A : Type i} {x y : A}
  → (p : x == y) → ap (idf A) p == p
book-2-2-2-iv = ap-idf

-- Lemma 2.3.1 (transport)

book-2-3-1 : ∀ {i j} {A : Type i} (P : A → Type j) {x y : A} (p : x == y)
  → (P x → P y)
book-2-3-1 = transport
