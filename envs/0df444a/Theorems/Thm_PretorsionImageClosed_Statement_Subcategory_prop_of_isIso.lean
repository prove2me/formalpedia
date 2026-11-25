-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_of_isIso
-- name    : PretorsionImageClosed.Statement.Subcategory.prop_of_isIso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:50:43.055557+00:00
-- url     : https://prove2.me/theorems/30f474e3-66d7-4faa-8763-55be1d3c408d
-- title:
--   Subcategory: prop of is Iso
-- statement:
--   The Subcategory construction uses the prop of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L84-L85
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L84-L85

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

theorem PretorsionImageClosed.Statement.Subcategory.prop_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] (hX : Z.prop X) : Z.prop Y := by sorry
