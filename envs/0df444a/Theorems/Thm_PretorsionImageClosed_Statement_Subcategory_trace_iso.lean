-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_iso
-- name    : PretorsionImageClosed.Statement.Subcategory.trace_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:28:29.251937+00:00
-- url     : https://prove2.me/theorems/63b4c70f-641d-5271-9ab5-fa1102880d14
-- title:
--   Subcategory: trace iso
-- statement:
--   The trace of an isomorphic object is the transported trace.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L320-L331
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L320-L331

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

theorem PretorsionImageClosed.Statement.Subcategory.trace_iso (hT : T.IsQuotientClosed) {X Y : C} (e : X ≅ Y) :
    T.trace Y = Subobject.mk ((T.trace X).arrow ≫ e.hom) := by sorry
