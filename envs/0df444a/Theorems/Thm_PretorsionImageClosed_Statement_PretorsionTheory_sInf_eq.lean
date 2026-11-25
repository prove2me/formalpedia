-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sInf_eq
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.sInf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:36:32.766748+00:00
-- url     : https://prove2.me/theorems/34b683a9-fc97-59f1-8d01-3938e2b622d4
-- title:
--   Pretorsion Theory: s Inf eq
-- statement:
--   The Pretorsion Theory construction uses the s Inf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L93-L93
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L93-L93

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.sInf_eq (S : Set (PretorsionTheory C)) : sInf S = meet S := by sorry
