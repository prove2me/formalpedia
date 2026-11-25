-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_eq_top_iff
-- name    : PretorsionImageClosed.Statement.Subcategory.trace_eq_top_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:27:08.83689+00:00
-- url     : https://prove2.me/theorems/742e5b6b-1c8b-4b95-b630-72bbbe82171c
-- title:
--   Subcategory: trace eq top iff
-- statement:
--   Proposition 2.10(3): `X ∈ T` iff `t_T(X) = X`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L172-L174
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L172-L174

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

theorem PretorsionImageClosed.Statement.Subcategory.trace_eq_top_iff (hT : T.IsQuotientClosed) : T.trace X = ⊤ ↔ T.prop X := by sorry
