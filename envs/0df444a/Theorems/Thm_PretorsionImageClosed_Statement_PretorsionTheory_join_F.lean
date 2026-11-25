-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_join_F
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.join_F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:41:54.165816+00:00
-- url     : https://prove2.me/theorems/549a5f5b-45e4-5480-aa0b-1f80de0e37fd
-- title:
--   Pretorsion Theory: join F
-- statement:
--   The Pretorsion Theory construction uses the join F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L101-L102
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L101-L102

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.join_F (S : Set (PretorsionTheory C)) : (join S).F = (meetT (PretorsionTheory.op '' S)).unop := by sorry
