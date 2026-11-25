-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_bot_le
-- name    : PretorsionImageClosed.Statement.Subcategory.bot_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:48:30.489125+00:00
-- url     : https://prove2.me/theorems/cc781a6f-10f7-4eb3-8728-564670d77a34
-- title:
--   Subcategory: bot le
-- statement:
--   The Subcategory construction uses the bot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L145-L145
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L145-L145

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

theorem PretorsionImageClosed.Statement.Subcategory.bot_le (Z : Subcategory C) : ⊥ ≤ Z := by sorry
