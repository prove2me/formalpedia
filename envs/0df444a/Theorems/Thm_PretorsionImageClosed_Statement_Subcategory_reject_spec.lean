-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_spec
-- name    : PretorsionImageClosed.Statement.Subcategory.reject_spec
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:28:18.606292+00:00
-- url     : https://prove2.me/theorems/579b8cb9-d377-4524-ada4-6e50b39e3f06
-- title:
--   Subcategory: reject spec
-- statement:
--   The Subcategory construction uses the reject spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L256-L260
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L256-L260

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

theorem PretorsionImageClosed.Statement.Subcategory.reject_spec :
    F.reject X ∈ F.quotientsIn X ∧
      ∀ K ∈ F.quotientsIn X, K ≤ F.reject X → K = F.reject X := by sorry
