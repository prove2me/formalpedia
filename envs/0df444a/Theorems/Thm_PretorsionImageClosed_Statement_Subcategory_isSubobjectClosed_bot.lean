-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_isSubobjectClosed_bot
-- name    : PretorsionImageClosed.Statement.Subcategory.isSubobjectClosed_bot
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:51:55.336535+00:00
-- url     : https://prove2.me/theorems/eaf13505-8651-520c-bd49-6612dfd3990f
-- title:
--   Subcategory: is Subobject Closed bot
-- statement:
--   The Subcategory construction uses the is Subobject Closed bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L199-L202
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L199-L202

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

theorem PretorsionImageClosed.Statement.Subcategory.isSubobjectClosed_bot : (⊥ : Subcategory C).IsSubobjectClosed := by sorry
