-- Prove2me | Theorems.Thm_P2M_PretorsionImageClosed_Subobject_factors_of_comp_cokernel___eq_zero_a7c3f47bcca4
-- name    : P2M_PretorsionImageClosed_Subobject_factors_of_comp_cokernel___eq_zero_a7c3f47bcca4
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:00:00.55189+00:00
-- url     : https://prove2.me/theorems/155b6429-456d-4a35-9372-80d27a4aa33c
-- title:
--   P2 M Pretorsion Image Closed Subobject factors of comp cokernel   eq zero a7c3f47bcca4: P2 M Pretorsion Image Closed Subobject factors of comp cokernel   eq zero a7c3f47bcca4
-- statement:
--   A morphism killed by `X → X/L` factors through `L`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L39-L42
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L39-L42

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

theorem P2M_PretorsionImageClosed_Subobject_factors_of_comp_cokernel___eq_zero_a7c3f47bcca4 {X W : C} (L : Subobject X) (f : W ⟶ X)
    (h : f ≫ cokernel.π L.arrow = 0) : L.Factors f := by sorry

alias «PretorsionImageClosed».«Subobject».«factors_of_comp_cokernel_π_eq_zero» := P2M_PretorsionImageClosed_Subobject_factors_of_comp_cokernel___eq_zero_a7c3f47bcca4
