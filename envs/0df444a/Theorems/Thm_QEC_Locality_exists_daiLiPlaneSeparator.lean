-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiPlaneSeparator
-- name    : QEC.Locality.exists_daiLiPlaneSeparator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:08:02.730677+00:00
-- url     : https://prove2.me/theorems/3b2614f5-c6fe-44c4-bfe1-ea65f88e4d42
-- title:
--   Locality: exists dai Li Plane Separator
-- statement:
--   DL24 Lemma 1 as an actual finite construction.  Every cut, its
--   orientation, its strict width, the strip bound, and both balance bounds are
--   constructed from the supplied finite point region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1476-L1599
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1476-L1599

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.exists_daiLiPlaneSeparator
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {ell : ℝ} (hRegion : region.Nonempty) (hTen : 10 ≤ region.card)
    (hEll : 0 < ell) (hScale : ell ≤ Real.sqrt region.card / 8) :
    (∃ lowerCut upperCut : ℝ,
      DaiLiVerticalCutsAvoid embedding region lowerCut upperCut ∧
      ell < upperCut - lowerCut ∧
      ((daiLiVerticalSeparatorStrip embedding region lowerCut upperCut).card : ℝ) ≤
        8 * ell * Real.sqrt region.card ∧
      10 * (daiLiVerticalSeparatorLower embedding region lowerCut).card ≤ 9 * region.card ∧
      10 * (daiLiVerticalSeparatorUpper embedding region upperCut).card ≤ 9 * region.card) ∨
    (∃ lowerCut upperCut : ℝ,
      DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut ∧
      ell < upperCut - lowerCut ∧
      ((daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut).card : ℝ) ≤
        8 * ell * Real.sqrt region.card ∧
      10 * (daiLiHorizontalSeparatorLower embedding region lowerCut).card ≤ 9 * region.card ∧
      10 * (daiLiHorizontalSeparatorUpper embedding region upperCut).card ≤ 9 * region.card) := by sorry
