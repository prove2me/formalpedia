-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_unop
-- name    : PretorsionImageClosed.Statement.Subcategory.op_unop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:01:14.187063+00:00
-- url     : https://prove2.me/theorems/26d4e479-7357-4ce5-ab8d-eea5b2a7712e
-- title:
--   Subcategory: op unop
-- statement:
--   The Subcategory construction uses the op unop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L169-L169
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L169-L169

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

theorem PretorsionImageClosed.Statement.Subcategory.op_unop (Z : Subcategory Cᵒᵖ) : Z.unop.op = Z := by sorry
