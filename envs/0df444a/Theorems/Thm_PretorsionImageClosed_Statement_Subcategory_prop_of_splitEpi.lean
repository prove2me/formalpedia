-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_of_splitEpi
-- name    : PretorsionImageClosed.Statement.Subcategory.prop_of_splitEpi
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:29:41.068992+00:00
-- url     : https://prove2.me/theorems/ad4795a8-dd1a-4a51-bcfa-7084c0a455d5
-- title:
--   Subcategory: prop of split Epi
-- statement:
--   The Subcategory construction uses the prop of split Epi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L90-L91
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L90-L91

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

theorem PretorsionImageClosed.Statement.Subcategory.prop_of_splitEpi {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] (hX : Z.prop X) : Z.prop Y := by sorry
