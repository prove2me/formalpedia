-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isTrivial_zero
-- name    : PretorsionImageClosed.Statement.isTrivial_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:23:07.476816+00:00
-- url     : https://prove2.me/theorems/db0c55bd-11f0-5738-b3fa-d0a4c1a350e7
-- title:
--   Statement: is Trivial zero
-- statement:
--   The Statement construction uses the is Trivial zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L275-L277
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L275-L277

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
open PretorsionImageClosed.Statement

theorem PretorsionImageClosed.Statement.isTrivial_zero [HasZeroObject C] (Zs : Subcategory C) {X Y : C} :
    IsTrivial Zs.prop (0 : X ⟶ Y) := by sorry
