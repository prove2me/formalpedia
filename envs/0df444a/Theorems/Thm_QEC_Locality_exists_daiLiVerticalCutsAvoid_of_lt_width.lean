-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiVerticalCutsAvoid_of_lt_width
-- name    : QEC.Locality.exists_daiLiVerticalCutsAvoid_of_lt_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:08:02.042382+00:00
-- url     : https://prove2.me/theorems/c818c5af-095e-4cfc-9af5-84905b89af3a
-- title:
--   Locality: exists dai Li Vertical Cuts Avoid of lt width
-- statement:
--   The source's perturbation step is available in the vertical orientation
--   as well, computed only from the finite parent support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1335-L1372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1335-L1372

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
omit [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.exists_daiLiVerticalCutsAvoid_of_lt_width
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {candidateLower candidateUpper threshold : ℝ}
    (hThreshold : 0 ≤ threshold)
    (hWidth : threshold < candidateUpper - candidateLower) :
    ∃ lowerCut upperCut : ℝ,
      candidateLower < lowerCut ∧ lowerCut < candidateUpper ∧
      candidateLower < upperCut ∧ upperCut < candidateUpper ∧
      threshold < upperCut - lowerCut ∧
      DaiLiVerticalCutsAvoid embedding region lowerCut upperCut := by sorry
