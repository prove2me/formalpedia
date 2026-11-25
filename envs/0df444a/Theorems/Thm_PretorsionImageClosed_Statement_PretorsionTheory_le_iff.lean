-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_le_iff
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:36:37.119747+00:00
-- url     : https://prove2.me/theorems/c7627811-b1d9-430d-8b67-d6fe032eb99e
-- title:
--   Pretorsion Theory: le iff
-- statement:
--   The Pretorsion Theory construction uses the le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L36-L36
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean#L36-L36

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_iff

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C]

theorem PretorsionImageClosed.Statement.PretorsionTheory.le_iff {P Q : PretorsionTheory C} : P ≤ Q ↔ P.LE Q := by sorry
