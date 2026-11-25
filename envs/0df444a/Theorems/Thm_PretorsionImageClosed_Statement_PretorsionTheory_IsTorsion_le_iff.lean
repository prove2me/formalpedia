-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_IsTorsion_le_iff
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.IsTorsion.le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:48:42.703863+00:00
-- url     : https://prove2.me/theorems/56df4cf3-1d98-4601-9cf0-b119139121eb
-- title:
--   Is Torsion: le iff
-- statement:
--   **Corollary 3.9**: torsion pairs are ordered by their first components, so the
--   first component determines a torsion pair.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L138-L152
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L138-L152

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_le_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_iff

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory ZeroObject
variable {C : Type*} [Category C] [Abelian C]
variable [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory

theorem PretorsionImageClosed.Statement.PretorsionTheory.IsTorsion.le_iff {P Q : PretorsionTheory C} (hP : P.IsTorsion) (hQ : Q.IsTorsion) :
    P ≤ Q ↔ P.T ≤ Q.T := by sorry
