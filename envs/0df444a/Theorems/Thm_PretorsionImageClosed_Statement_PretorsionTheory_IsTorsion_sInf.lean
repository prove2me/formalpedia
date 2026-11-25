-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_IsTorsion_sInf
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.IsTorsion.sInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:52:22.314765+00:00
-- url     : https://prove2.me/theorems/b6e71754-7f33-40c1-b353-a8d9e3832905
-- title:
--   Is Torsion: s Inf
-- statement:
--   **Corollary 3.9**: nonempty meets of torsion pairs are torsion pairs.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L109-L113
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L109-L113

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.IsTorsion.sInf {S : Set (PretorsionTheory C)} (hne : S.Nonempty)
    (h : ∀ P ∈ S, P.IsTorsion) : (sInf S).IsTorsion := by sorry
