-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_le
-- name    : PretorsionImageClosed.Statement.Subcategory.reject_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:26:47.972146+00:00
-- url     : https://prove2.me/theorems/68ec0e83-509a-49d9-877a-6e6897e5072b
-- title:
--   Subcategory: reject le
-- statement:
--   Proposition 2.10(2): for subobject-closed `F`, the reject is the smallest
--   subobject `K` with `X/K` in `F`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L272-L276
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L272-L276

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [Abelian C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (T : Subcategory C) (X : C)
variable (F : Subcategory C)
variable [HasLength C]
variable {T X}
variable (X)
variable {F X}

theorem PretorsionImageClosed.Statement.Subcategory.reject_le (hF : F.IsSubobjectClosed) {K : Subobject X} (hK : F.prop (cokernel K.arrow)) :
    F.reject X ≤ K := by sorry
