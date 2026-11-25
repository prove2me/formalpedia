-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isLUB_join
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.isLUB_join
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:38:03.952964+00:00
-- url     : https://prove2.me/theorems/8da47b24-03ad-4da1-9637-577d89b2363f
-- title:
--   Pretorsion Theory: is LUB join
-- statement:
--   The Pretorsion Theory construction uses the is LUB join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L79-L86
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L79-L86

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.isLUB_join (S : Set (PretorsionTheory C)) : IsLUB S (join S) := by sorry
