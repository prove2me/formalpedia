-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
-- name    : PretorsionImageClosed.Statement.Subcategory.prop_cokernel_reject
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:26:43.636395+00:00
-- url     : https://prove2.me/theorems/56f46f3e-1e7c-4ac7-936d-1361ae4916fa
-- title:
--   Subcategory: prop cokernel reject
-- statement:
--   The Subcategory construction uses the prop cokernel reject property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L262-L262
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L262-L262

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
variable (X)

theorem PretorsionImageClosed.Statement.Subcategory.prop_cokernel_reject : F.prop (cokernel (F.reject X).arrow) := by sorry
