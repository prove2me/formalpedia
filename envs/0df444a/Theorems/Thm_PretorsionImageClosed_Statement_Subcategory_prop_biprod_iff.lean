-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biprod_iff
-- name    : PretorsionImageClosed.Statement.Subcategory.prop_biprod_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:21:51.176711+00:00
-- url     : https://prove2.me/theorems/bf9ea719-0ba9-47cf-a6c5-6b72069dca71
-- title:
--   Subcategory: prop biprod iff
-- statement:
--   The Subcategory construction uses the prop biprod iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L99-L100
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L99-L100

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

theorem PretorsionImageClosed.Statement.Subcategory.prop_biprod_iff {X Y : C} : Z.prop (X ⊞ Y) ↔ Z.prop X ∧ Z.prop Y := by sorry
