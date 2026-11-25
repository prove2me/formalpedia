-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_eq_bot_iff
-- name    : PretorsionImageClosed.Statement.Subcategory.reject_eq_bot_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:27:05.951411+00:00
-- url     : https://prove2.me/theorems/0cc6f20c-8c7c-4193-89f7-ed2eff6ac26f
-- title:
--   Subcategory: reject eq bot iff
-- statement:
--   Proposition 2.10(3): `X ∈ F` iff `r_F(X) = 0`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L279-L281
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L279-L281

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
variable {F X}

theorem PretorsionImageClosed.Statement.Subcategory.reject_eq_bot_iff (hF : F.IsSubobjectClosed) : F.reject X = ⊥ ↔ F.prop X := by sorry
