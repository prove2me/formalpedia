-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_mk_ofLE_mk_comp_arrow
-- name    : PretorsionImageClosed.Subobject.mk_ofLE_mk_comp_arrow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:20:21.853175+00:00
-- url     : https://prove2.me/theorems/b67769eb-0ab0-407f-ac54-d48fffd174aa
-- title:
--   Subobject: mk of LE mk comp arrow
-- statement:
--   The subobject of `S` given by `mk (K.arrow ≫ S.arrow) ≤ S` is `K` again.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L107-L112
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L107-L112

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

theorem PretorsionImageClosed.Subobject.mk_ofLE_mk_comp_arrow {X : C} (S : Subobject X) (K : Subobject (S : C)) :
    Subobject.mk (Subobject.ofLE _ S (Subobject.mk_comp_arrow_le S K)) = K := by sorry
