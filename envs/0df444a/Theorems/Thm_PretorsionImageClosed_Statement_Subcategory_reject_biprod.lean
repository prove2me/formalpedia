-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_biprod
-- name    : PretorsionImageClosed.Statement.Subcategory.reject_biprod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:54:07.589624+00:00
-- url     : https://prove2.me/theorems/271ac901-c4d3-470e-8ba9-fbb180149903
-- title:
--   Subcategory: reject biprod
-- statement:
--   Proposition 2.10(4): the reject of a direct sum is the direct sum of the rejects.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L350-L379
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L350-L379

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
open PretorsionImageClosed PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C}

theorem PretorsionImageClosed.Statement.Subcategory.reject_biprod (hF : F.IsSubobjectClosed) (Y₁ Y₂ : C) :
    F.reject (Y₁ ⊞ Y₂) = Subobject.mk (biprod.map (F.reject Y₁).arrow (F.reject Y₂).arrow) := by sorry
