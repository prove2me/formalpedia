-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_push_reject_le
-- name    : PretorsionImageClosed.Statement.Subcategory.push_reject_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:54:48.297434+00:00
-- url     : https://prove2.me/theorems/4cc6e8d8-5b64-4cda-8a5f-6e2de24ec457
-- title:
--   Subcategory: push reject le
-- statement:
--   Proposition 2.10(5): for a subobject `W ⊆ X`, `r(W) ⊆ r(X)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L387-L392
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L387-L392

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

theorem PretorsionImageClosed.Statement.Subcategory.push_reject_le (hF : F.IsSubobjectClosed) {X : C} (W : Subobject X) :
    Subobject.push W (F.reject (W : C)) ≤ F.reject X := by sorry
