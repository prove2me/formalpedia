-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_minimal
-- name    : PretorsionImageClosed.Statement.Subcategory.reject_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:38:08.440934+00:00
-- url     : https://prove2.me/theorems/8aef23d2-db6a-4f33-be0d-aac8dcb7ee30
-- title:
--   Subcategory: reject minimal
-- statement:
--   The Subcategory construction uses the reject minimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L264-L266
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L264-L266

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

theorem PretorsionImageClosed.Statement.Subcategory.reject_minimal {K : Subobject X} (hK : F.prop (cokernel K.arrow)) (h : K ≤ F.reject X) :
    K = F.reject X := by sorry
