-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sInf_F_prop
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.sInf_F_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:42:44.987299+00:00
-- url     : https://prove2.me/theorems/62b930a4-f1fe-4fc4-bf01-889e575966c2
-- title:
--   Pretorsion Theory: s Inf F prop
-- statement:
--   The Pretorsion Theory construction uses the s Inf F prop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L115-L124
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L115-L124

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.sInf_F_prop (S : Set (PretorsionTheory C)) :
    (sInf S).F.prop = ⨅ (F : Subcategory C)
      (_ : IsPretorsionTheory (⨅ P ∈ S, P.T.prop) F.prop ∧ ∀ P ∈ S, P.F.prop ≤ F.prop), F.prop := by sorry
