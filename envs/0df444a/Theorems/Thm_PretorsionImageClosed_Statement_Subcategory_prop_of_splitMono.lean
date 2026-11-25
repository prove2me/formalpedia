-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_of_splitMono
-- name    : PretorsionImageClosed.Statement.Subcategory.prop_of_splitMono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:21:35.341976+00:00
-- url     : https://prove2.me/theorems/b1ad5812-c384-4327-bc77-e1e4eed12314
-- title:
--   Subcategory: prop of split Mono
-- statement:
--   The Subcategory construction uses the prop of split Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L87-L88
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L87-L88

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

theorem PretorsionImageClosed.Statement.Subcategory.prop_of_splitMono {X Y : C} (f : X ⟶ Y) [IsSplitMono f] (hY : Z.prop Y) : Z.prop X := by sorry
