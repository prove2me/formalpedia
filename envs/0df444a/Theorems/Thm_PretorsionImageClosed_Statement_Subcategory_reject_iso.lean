-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_iso
-- name    : PretorsionImageClosed.Statement.Subcategory.reject_iso
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:28:32.031157+00:00
-- url     : https://prove2.me/theorems/a09a0742-1c9e-535a-aec8-1e69f50dcc15
-- title:
--   Subcategory: reject iso
-- statement:
--   The reject of an isomorphic object is the transported reject.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L334-L345
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L334-L345

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

theorem PretorsionImageClosed.Statement.Subcategory.reject_iso (hF : F.IsSubobjectClosed) {X Y : C} (e : X ≅ Y) :
    F.reject Y = Subobject.mk ((F.reject X).arrow ≫ e.hom) := by sorry
