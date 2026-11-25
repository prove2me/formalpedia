-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_bot_eq
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.bot_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:41:04.953045+00:00
-- url     : https://prove2.me/theorems/82120a57-70bf-4f60-a3b3-df8704149e5c
-- title:
--   Pretorsion Theory: bot eq
-- statement:
--   The Pretorsion Theory construction uses the bot eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L173-L175
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L173-L175

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C]
variable [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory

theorem PretorsionImageClosed.Statement.PretorsionTheory.bot_eq : (⊥ : PretorsionTheory C) = botPT := by sorry
