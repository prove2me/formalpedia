-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_IsTorsion_eq_of_T_eq
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.IsTorsion.eq_of_T_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:52:46.434882+00:00
-- url     : https://prove2.me/theorems/8b6d48ea-d653-4cb2-ba32-a1ae764f8e77
-- title:
--   Is Torsion: eq of T eq
-- statement:
--   The Is Torsion construction uses the eq of T eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L154-L156
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L154-L156

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
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

theorem PretorsionImageClosed.Statement.PretorsionTheory.IsTorsion.eq_of_T_eq {P Q : PretorsionTheory C} (hP : P.IsTorsion) (hQ : Q.IsTorsion)
    (h : P.T = Q.T) : P = Q := by sorry
