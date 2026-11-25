-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_lt
-- name    : PretorsionImageClosed.LinearQuiver.coord_eq_zero_of_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:06:57.169442+00:00
-- url     : https://prove2.me/theorems/6fa660a7-4175-579d-bd0c-95791dbaca6b
-- title:
--   Linear Quiver: coord eq zero of lt
-- statement:
--   If `d < b`, every morphism `M_{c,d} ⟶ M_{a,b}` is zero.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L136-L142
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L136-L142

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

theorem PretorsionImageClosed.LinearQuiver.coord_eq_zero_of_lt {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (hdb : d < b)
    (i : Fin n) : coord η i = 0 := by sorry
