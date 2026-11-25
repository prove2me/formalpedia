-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_middle
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.op_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:41:03.389359+00:00
-- url     : https://prove2.me/theorems/aa306817-9866-5742-ad30-755da6b062a7
-- title:
--   Pretorsion Theory: op middle
-- statement:
--   The Pretorsion Theory construction uses the op middle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L138-L141
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L138-L141

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory
variable (S : Set (PretorsionTheory C)) (Z : Subcategory C)
variable {S Z} {P₀ : PretorsionTheory C} (hP₀ : P₀ ∈ S) (hS : ∀ P ∈ S, P.middle = Z.prop)
include hP₀ hS
omit hP₀ hS

theorem PretorsionImageClosed.Statement.PretorsionTheory.op_middle (P : PretorsionTheory C) : P.op.middle = P.middle.op := by sorry
