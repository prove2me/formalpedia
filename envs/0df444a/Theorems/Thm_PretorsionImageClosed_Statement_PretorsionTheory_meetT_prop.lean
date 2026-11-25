-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meetT_prop
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.meetT_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:37:02.246801+00:00
-- url     : https://prove2.me/theorems/3f1118a5-e154-554f-945c-4da65935df83
-- title:
--   Pretorsion Theory: meet T prop
-- statement:
--   The Pretorsion Theory construction uses the meet T prop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L104-L109
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L104-L109

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.meetT_prop (S : Set (PretorsionTheory C)) : (meetT S).prop = ⨅ P ∈ S, P.T.prop := by sorry
