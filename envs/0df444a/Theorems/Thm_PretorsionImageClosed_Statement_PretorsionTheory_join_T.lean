-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_join_T
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.join_T
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:42:15.144438+00:00
-- url     : https://prove2.me/theorems/52d5a39c-c9bb-4c75-9c39-f99abfbe19de
-- title:
--   Pretorsion Theory: join T
-- statement:
--   The Pretorsion Theory construction uses the join T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L98-L99
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L98-L99

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.join_T (S : Set (PretorsionTheory C)) : (join S).T = (meet (PretorsionTheory.op '' S)).F.unop := by sorry
