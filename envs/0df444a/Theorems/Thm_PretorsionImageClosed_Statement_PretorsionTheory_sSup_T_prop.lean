-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sSup_T_prop
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.sSup_T_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:43:41.660276+00:00
-- url     : https://prove2.me/theorems/0ed767e7-0588-5813-b938-5c90ccad4e21
-- title:
--   Pretorsion Theory: s Sup T prop
-- statement:
--   The Pretorsion Theory construction uses the s Sup T prop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L138-L159
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L138-L159

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.sSup_T_prop (S : Set (PretorsionTheory C)) :
    (sSup S).T.prop = ⨅ (T : Subcategory C)
      (_ : IsPretorsionTheory T.prop (⨅ P ∈ S, P.F.prop) ∧ ∀ P ∈ S, P.T.prop ≤ T.prop), T.prop := by sorry
