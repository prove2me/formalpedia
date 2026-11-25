-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_prop
-- name    : PretorsionImageClosed.Statement.Subcategory.op_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:01:25.062801+00:00
-- url     : https://prove2.me/theorems/8b525a35-fa00-44e8-8244-026f794414ee
-- title:
--   Subcategory: op prop
-- statement:
--   The Subcategory construction uses the op prop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L163-L163
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L163-L163

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

theorem PretorsionImageClosed.Statement.Subcategory.op_prop (Z : Subcategory C) : Z.op.prop = Z.prop.op := by sorry

attribute [defeq] PretorsionImageClosed.Statement.Subcategory.op_prop
