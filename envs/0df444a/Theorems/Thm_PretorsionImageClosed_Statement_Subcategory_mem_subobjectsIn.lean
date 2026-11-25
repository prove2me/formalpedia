-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_mem_subobjectsIn
-- name    : PretorsionImageClosed.Statement.Subcategory.mem_subobjectsIn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:48:30.99728+00:00
-- url     : https://prove2.me/theorems/fd39b152-a8df-4112-8257-1c3b0754fcc1
-- title:
--   Subcategory: mem subobjects In
-- statement:
--   The Subcategory construction uses the mem subobjects In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L60-L60
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L60-L60

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

theorem PretorsionImageClosed.Statement.Subcategory.mem_subobjectsIn {S : Subobject X} : S ∈ T.subobjectsIn X ↔ T.prop (S : C) := by sorry
