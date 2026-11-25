-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_unop
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.op_unop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:01:31.986263+00:00
-- url     : https://prove2.me/theorems/4c63b514-6e45-4c83-9747-39e251c0f6ef
-- title:
--   Pretorsion Theory: op unop
-- statement:
--   The Pretorsion Theory construction uses the op unop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L195-L196
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L195-L196

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.op_unop (P : PretorsionTheory Cᵒᵖ) : P.unop.op = P := by sorry
