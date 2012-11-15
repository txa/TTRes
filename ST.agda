module ST where

open import Data.Nat 
open import Data.Bool

data Ty : Set where
  bool : Ty
  nat : Ty

⟦_⟧ : Ty → Set
⟦ bool ⟧ = Bool
⟦ nat ⟧ = ℕ

data W : Set where
  ε : W
  _,_ : W → Ty → W

infix 4 _≤W_

data _≤W_ : W → W → Set where
  refl : ∀ {w} → w ≤W w
  right : ∀ {w w' σ} → w ≤W w' → w ≤W w' , σ
  weak : ∀ {w w' σ} → w ≤W w' → w , σ ≤W w' , σ

transW : ∀ {w w' w''} → w ≤W w' → w' ≤W w'' → w ≤W w''
transW p refl = p
transW p (right q) = right (transW p q)
transW refl (weak q) = weak q
transW (right p) (weak q) = {!!}
transW (weak p) (weak q) = {!!}

