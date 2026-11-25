-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_mk_ofLE_push
-- name    : PretorsionImageClosed.Subobject.mk_ofLE_push
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:47:39.31925+00:00
-- url     : https://prove2.me/theorems/fae050ca-f905-5576-8bc2-791af7df1547
-- title:
--   Subobject: mk of LE push
-- statement:
--   The subobject of `S` given by `push S K ≤ S` is `K` again.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L230-L234
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L230-L234

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
variable {C : Type*} [Category C] [Abelian C] {X : C} (S : Subobject X) (K : Subobject (S : C))

theorem PretorsionImageClosed.Subobject.mk_ofLE_push :
    Subobject.mk (Subobject.ofLE _ S (Subobject.push_le S K)) = K := by sorry
