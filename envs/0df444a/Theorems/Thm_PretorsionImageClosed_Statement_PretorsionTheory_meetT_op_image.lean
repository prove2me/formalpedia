-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meetT_op_image
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.meetT_op_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:38:04.966662+00:00
-- url     : https://prove2.me/theorems/a4173806-0a81-4c42-b71b-e34ca9316aa9
-- title:
--   Pretorsion Theory: meet T op image
-- statement:
--   The Pretorsion Theory construction uses the meet T op image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L126-L136
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L126-L136

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.meetT_op_image (S : Set (PretorsionTheory C)) :
    (meetT (PretorsionTheory.op '' S)).prop = (⨅ P ∈ S, P.F.prop).op := by sorry
