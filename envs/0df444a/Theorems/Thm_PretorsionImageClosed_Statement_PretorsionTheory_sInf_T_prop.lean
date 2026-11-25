-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sInf_T_prop
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.sInf_T_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:42:24.528533+00:00
-- url     : https://prove2.me/theorems/7afb3b38-44cb-46c4-95c5-2cc135e315f4
-- title:
--   Pretorsion Theory: s Inf T prop
-- statement:
--   The Pretorsion Theory construction uses the s Inf T prop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L111-L113
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L111-L113

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.sInf_T_prop (S : Set (PretorsionTheory C)) : (sInf S).T.prop = ⨅ P ∈ S, P.T.prop := by sorry
