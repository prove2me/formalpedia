-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_factors_comp_mono
-- name    : PretorsionImageClosed.Statement.Subcategory.trace_factors_comp_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:51:12.578149+00:00
-- url     : https://prove2.me/theorems/7b104b52-a5b7-59bc-a105-35d07c060e63
-- title:
--   Subcategory: trace factors comp mono
-- statement:
--   Proposition 2.10(5): the trace is monotone, in the form that the trace of a
--   subobject maps into the trace.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L194-L196
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L194-L196

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

theorem PretorsionImageClosed.Statement.Subcategory.trace_factors_comp_mono (hT : T.IsQuotientClosed) {W : C} (f : W ⟶ X) [Mono f] :
    (T.trace X).Factors ((T.trace W).arrow ≫ f) := by sorry
