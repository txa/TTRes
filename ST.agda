module ST where

open import Data.Nat
open import Data.Bool

data Ty : Set where
  bool : Ty
  nat : Ty

⟦_⟧ : Ty → Set
⟦ bool ⟧ = Bool
⟦ nat ⟧ = ℕ



