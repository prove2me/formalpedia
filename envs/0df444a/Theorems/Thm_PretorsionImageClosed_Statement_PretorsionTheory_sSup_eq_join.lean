-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sSup_eq_join
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.sSup_eq_join
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:37:47.607898+00:00
-- url     : https://prove2.me/theorems/db3f000d-8223-4284-865d-60e30ae2f9da
-- title:
--   Pretorsion Theory: s Sup eq join
-- statement:
--   The Pretorsion Theory construction uses the s Sup eq join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L88-L89
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L88-L89

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.sSup_eq_join (S : Set (PretorsionTheory C)) : sSup S = join S := by sorry
