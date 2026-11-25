-- Prove2me | Theorems.Thm_P2M_PretorsionImageClosed_Subobject_le_of_arrow_comp_cokernel___eq_zero_a0c37c2dae50
-- name    : P2M_PretorsionImageClosed_Subobject_le_of_arrow_comp_cokernel___eq_zero_a0c37c2dae50
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:20:05.575165+00:00
-- url     : https://prove2.me/theorems/70a859fd-ae6e-42be-90c1-6d14a77084bf
-- title:
--   P2 M Pretorsion Image Closed Subobject le of arrow comp cokernel   eq zero a0c37c2dae50: P2 M Pretorsion Image Closed Subobject le of arrow comp cokernel   eq zero a0c37c2dae50
-- statement:
--   A subobject killed by `X → X/L` is contained in `L`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L45-L47
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L45-L47

module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]

theorem P2M_PretorsionImageClosed_Subobject_le_of_arrow_comp_cokernel___eq_zero_a0c37c2dae50 {X : C} {S L : Subobject X}
    (h : S.arrow ≫ cokernel.π L.arrow = 0) : S ≤ L := by sorry

alias «PretorsionImageClosed».«Subobject».«le_of_arrow_comp_cokernel_π_eq_zero» := P2M_PretorsionImageClosed_Subobject_le_of_arrow_comp_cokernel___eq_zero_a0c37c2dae50
