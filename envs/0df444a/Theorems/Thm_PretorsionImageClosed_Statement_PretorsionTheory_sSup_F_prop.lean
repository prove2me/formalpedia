-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sSup_F_prop
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.sSup_F_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:43:13.65238+00:00
-- url     : https://prove2.me/theorems/9367a542-58c9-4c79-9a11-29eccbec0cd5
-- title:
--   Pretorsion Theory: s Sup F prop
-- statement:
--   The Pretorsion Theory construction uses the s Sup F prop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L161-L163
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L161-L163

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.sSup_F_prop (S : Set (PretorsionTheory C)) : (sSup S).F.prop = ⨅ P ∈ S, P.F.prop := by sorry
