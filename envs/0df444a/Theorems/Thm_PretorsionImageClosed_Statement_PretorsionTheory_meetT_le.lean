-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meetT_le
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.meetT_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:40:18.46717+00:00
-- url     : https://prove2.me/theorems/2db03957-bc19-54c7-b563-0252de4a02d9
-- title:
--   Pretorsion Theory: meet T le
-- statement:
--   The Pretorsion Theory construction uses the meet T le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L35-L36
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L35-L36

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.meetT_le {P : PretorsionTheory C} (hP : P ∈ S) : (meetT S).prop ≤ P.T.prop := by sorry
