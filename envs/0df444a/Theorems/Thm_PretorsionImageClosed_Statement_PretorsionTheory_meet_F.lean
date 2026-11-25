-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meet_F
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.meet_F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:38:04.414167+00:00
-- url     : https://prove2.me/theorems/d32bae32-f66a-474c-8117-ae7ebf366049
-- title:
--   Pretorsion Theory: meet F
-- statement:
--   The Pretorsion Theory construction uses the meet F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L95-L96
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L95-L96

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.meet_F (S : Set (PretorsionTheory C)) :
    (meet S).F = Subcategory.iInf (fun F : MeetPartners S => F.1) := by sorry
