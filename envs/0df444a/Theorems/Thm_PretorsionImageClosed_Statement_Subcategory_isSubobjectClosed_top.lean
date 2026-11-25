-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_isSubobjectClosed_top
-- name    : PretorsionImageClosed.Statement.Subcategory.isSubobjectClosed_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:51:42.78451+00:00
-- url     : https://prove2.me/theorems/ebde809a-0aa2-53f1-8014-f798d0500389
-- title:
--   Subcategory: is Subobject Closed top
-- statement:
--   The Subcategory construction uses the is Subobject Closed top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L192-L192
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L192-L192

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

theorem PretorsionImageClosed.Statement.Subcategory.isSubobjectClosed_top : (⊤ : Subcategory C).IsSubobjectClosed := by sorry
