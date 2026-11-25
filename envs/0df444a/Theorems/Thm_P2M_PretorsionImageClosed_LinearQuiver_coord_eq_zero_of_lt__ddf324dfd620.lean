-- Prove2me | Theorems.Thm_P2M_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_lt__ddf324dfd620
-- name    : P2M_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_lt__ddf324dfd620
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:04:09.818164+00:00
-- url     : https://prove2.me/theorems/c1f6952d-dfc1-4c67-a579-674783df85db
-- title:
--   P2 M Pretorsion Image Closed Linear Quiver coord eq zero of lt  ddf324dfd620: P2 M Pretorsion Image Closed Linear Quiver coord eq zero of lt  ddf324dfd620
-- statement:
--   If `c < a`, every morphism `M_{c,d} ⟶ M_{a,b}` is zero.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L145-L153
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L145-L153

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

theorem P2M_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_lt__ddf324dfd620 {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (hca : c < a)
    (i : Fin n) : coord η i = 0 := by sorry

alias «PretorsionImageClosed».«LinearQuiver».«coord_eq_zero_of_lt'» := P2M_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_lt__ddf324dfd620
