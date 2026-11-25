-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biprod_left
-- name    : PretorsionImageClosed.Statement.Subcategory.prop_biprod_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:04:19.902995+00:00
-- url     : https://prove2.me/theorems/d130b0a6-7509-4970-a1b2-582273b7b4ef
-- title:
--   Subcategory: prop biprod left
-- statement:
--   The Subcategory construction uses the prop biprod left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L93-L94
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L93-L94

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

theorem PretorsionImageClosed.Statement.Subcategory.prop_biprod_left {X Y : C} (h : Z.prop (X ⊞ Y)) : Z.prop X := by sorry
