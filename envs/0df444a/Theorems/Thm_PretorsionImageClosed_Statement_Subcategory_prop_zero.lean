-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_zero
-- name    : PretorsionImageClosed.Statement.Subcategory.prop_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:56:21.217605+00:00
-- url     : https://prove2.me/theorems/aaa9ecd2-ca26-4bfe-b084-a8434f187a9d
-- title:
--   Subcategory: prop zero
-- statement:
--   The Subcategory construction uses the prop zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L102-L103
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L102-L103

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
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory C)

theorem PretorsionImageClosed.Statement.Subcategory.prop_zero [HasZeroObject C] : Z.prop 0 := by sorry
