{-# OPTIONS --without-K #-}

module book.HoTTBook where

open import HoTT public

-- Lemma 2.1.1

book-2-1-1 : ∀ {i} {A : Type i} {x y : A} → (x == y) → (y == x)
book-2-1-1 = !

-- Lemma 2.1.2

book-2-1-2 : ∀ {i} {A : Type i} {x y z : A} → (x == y) → (y == z) → (x == z)
book-2-1-2 = _∙_

-- Lemma 2.1.4

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

book-2-1-4-iv : ∀ {i} {A : Type i} {x y z w : A} (p : x == y) (q : y == z) (r : z == w) →
                p ∙ (q ∙ r) == (p ∙ q) ∙ r
book-2-1-4-iv p q r = ! (∙-assoc p q r)

-- Theorem 2.1.6 (Eckmann-Hilton): not all here yet


