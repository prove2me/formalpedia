-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_unop_op
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.unop_op
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:32.779805+00:00
-- url     : https://prove2.me/theorems/6888c6f4-6efa-4926-882b-b0a28db6cc66
-- title:
--   Pretorsion Theory: unop op
-- statement:
--   The Pretorsion Theory construction uses the unop op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L192-L193
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L192-L193

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.unop_op (P : PretorsionTheory C) : P.op.unop = P := by sorry
