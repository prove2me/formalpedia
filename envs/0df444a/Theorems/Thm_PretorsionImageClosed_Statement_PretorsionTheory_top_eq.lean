-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_top_eq
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.top_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:41:00.337091+00:00
-- url     : https://prove2.me/theorems/80b30cfc-f2ed-4513-8b92-f901fe375484
-- title:
--   Pretorsion Theory: top eq
-- statement:
--   The Pretorsion Theory construction uses the top eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L177-L179
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L177-L179

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.top_eq : (⊤ : PretorsionTheory C) = topPT := by sorry
