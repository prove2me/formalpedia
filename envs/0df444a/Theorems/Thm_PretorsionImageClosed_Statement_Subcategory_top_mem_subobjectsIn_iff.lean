-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_top_mem_subobjectsIn_iff
-- name    : PretorsionImageClosed.Statement.Subcategory.top_mem_subobjectsIn_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:29:09.000492+00:00
-- url     : https://prove2.me/theorems/5bc1a679-fc90-50de-b7b0-75f71bc8a119
-- title:
--   Subcategory: top mem subobjects In iff
-- statement:
--   The Subcategory construction uses the top mem subobjects In iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L65-L66
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L65-L66

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

theorem PretorsionImageClosed.Statement.Subcategory.top_mem_subobjectsIn_iff : ⊤ ∈ T.subobjectsIn X ↔ T.prop X := by sorry
