-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_push_trace_le
-- name    : PretorsionImageClosed.Statement.Subcategory.push_trace_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:54:06.48797+00:00
-- url     : https://prove2.me/theorems/f97032b4-ad3e-4dc7-a12a-08b77fa9b33e
-- title:
--   Subcategory: push trace le
-- statement:
--   Proposition 2.10(5): for a subobject `W ⊆ X`, `t(W) ⊆ t(X)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L382-L384
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L382-L384

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

theorem PretorsionImageClosed.Statement.Subcategory.push_trace_le (hT : T.IsQuotientClosed) {X : C} (W : Subobject X) :
    Subobject.push W (T.trace (W : C)) ≤ T.trace X := by sorry
