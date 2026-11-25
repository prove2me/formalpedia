-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_le_iff
-- name    : PretorsionImageClosed.Statement.Subcategory.trace_le_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:51:42.588504+00:00
-- url     : https://prove2.me/theorems/c5a2fca6-14e2-4e5a-82c8-83af718db6bd
-- title:
--   Subcategory: trace le iff
-- statement:
--   Definition 2.7: the trace is the sum of the images of all morphisms from
--   objects of `T`, in the form: a subobject contains the trace iff every morphism
--   from an object of `T` factors through it.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L187-L190
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L187-L190

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

theorem PretorsionImageClosed.Statement.Subcategory.trace_le_iff (hT : T.IsQuotientClosed) {S : Subobject X} :
    T.trace X ≤ S ↔ ∀ {Y : C} (f : Y ⟶ X), T.prop Y → S.Factors f := by sorry
