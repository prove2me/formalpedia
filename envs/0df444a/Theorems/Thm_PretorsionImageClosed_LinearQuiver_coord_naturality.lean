-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_naturality
-- name    : PretorsionImageClosed.LinearQuiver.coord_naturality
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:22:29.368787+00:00
-- url     : https://prove2.me/theorems/a1ce7e0a-2e6b-48d6-b754-33c8f992eead
-- title:
--   Linear Quiver: coord naturality
-- statement:
--   The naturality equation in coordinates: for `i ≤ j` and `i ∈ [c, d]`,
--   `(if j ≤ d then coord η j else 0) = if j ≤ b then coord η i else 0`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L108-L131
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L108-L131

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable (k : Type u) [Field k] {n : ℕ}
variable {k}

theorem PretorsionImageClosed.LinearQuiver.coord_naturality {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) {i j : Fin n}
    (hij : i ≤ j) (hi : c ≤ i ∧ i ≤ d) :
    (if j ≤ d then coord η j else 0) = if j ≤ b then coord η i else 0 := by sorry
