-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_isQuotientClosed_bot
-- name    : PretorsionImageClosed.Statement.Subcategory.isQuotientClosed_bot
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:17:13.460417+00:00
-- url     : https://prove2.me/theorems/b1e05c5a-282e-4d28-9944-26f91e6d0099
-- title:
--   Subcategory: is Quotient Closed bot
-- statement:
--   The Subcategory construction uses the is Quotient Closed bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L194-L197
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L194-L197

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

theorem PretorsionImageClosed.Statement.Subcategory.isQuotientClosed_bot : (⊥ : Subcategory C).IsQuotientClosed := by sorry
