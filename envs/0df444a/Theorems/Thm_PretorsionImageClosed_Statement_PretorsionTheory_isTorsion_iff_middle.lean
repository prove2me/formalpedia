-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isTorsion_iff_middle
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.isTorsion_iff_middle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:42:02.140301+00:00
-- url     : https://prove2.me/theorems/8f57108e-08b2-5d86-97c4-1da48d18922a
-- title:
--   Pretorsion Theory: is Torsion iff middle
-- statement:
--   The Pretorsion Theory construction uses the is Torsion iff middle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L97-L106
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L97-L106

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.isTorsion_iff_middle (P : PretorsionTheory C) :
    P.IsTorsion ↔ P.middle = (⊥ : Subcategory C).prop := by sorry
