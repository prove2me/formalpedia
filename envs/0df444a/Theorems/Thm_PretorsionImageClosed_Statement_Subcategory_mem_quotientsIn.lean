-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_mem_quotientsIn
-- name    : PretorsionImageClosed.Statement.Subcategory.mem_quotientsIn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:48:45.70018+00:00
-- url     : https://prove2.me/theorems/f33145e1-9261-4b8d-a154-a5a7e118b265
-- title:
--   Subcategory: mem quotients In
-- statement:
--   The Subcategory construction uses the mem quotients In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L80-L81
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L80-L81

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

theorem PretorsionImageClosed.Statement.Subcategory.mem_quotientsIn {K : Subobject X} : K ∈ F.quotientsIn X ↔ F.prop (cokernel K.arrow) := by sorry
