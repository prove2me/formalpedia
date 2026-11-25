-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_le_of_coord_ne_zero
-- name    : PretorsionImageClosed.LinearQuiver.le_of_coord_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:30:36.828488+00:00
-- url     : https://prove2.me/theorems/93aaad0f-4e71-48d6-9b95-0db55e180249
-- title:
--   Linear Quiver: le of coord ne zero
-- statement:
--   A morphism between intervals with a nonzero coordinate forces the
--   inequalities `a ≤ c` and `b ≤ d`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L165-L171
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L165-L171

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.le_of_coord_ne_zero {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) {i : Fin n}
    (h : coord η i ≠ 0) : a ≤ c ∧ b ≤ d := by sorry
