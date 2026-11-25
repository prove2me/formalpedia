-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_unop_prop
-- name    : PretorsionImageClosed.Statement.Subcategory.unop_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:01:09.712415+00:00
-- url     : https://prove2.me/theorems/3ea4e0cd-8149-4a8b-b368-8658ed746dfb
-- title:
--   Subcategory: unop prop
-- statement:
--   The Subcategory construction uses the unop prop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L165-L165
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L165-L165

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Opposite
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] [Abelian C]

theorem PretorsionImageClosed.Statement.Subcategory.unop_prop (Z : Subcategory Cᵒᵖ) : Z.unop.prop = Z.prop.unop := by sorry

attribute [defeq] PretorsionImageClosed.Statement.Subcategory.unop_prop
