-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_isQuotientClosed_top
-- name    : PretorsionImageClosed.Statement.Subcategory.isQuotientClosed_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:51:38.867843+00:00
-- url     : https://prove2.me/theorems/d5a9f7d2-6836-5ec4-bede-c8caf50dcbae
-- title:
--   Subcategory: is Quotient Closed top
-- statement:
--   The Subcategory construction uses the is Quotient Closed top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L190-L190
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L190-L190

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

theorem PretorsionImageClosed.Statement.Subcategory.isQuotientClosed_top : (⊤ : Subcategory C).IsQuotientClosed := by sorry
