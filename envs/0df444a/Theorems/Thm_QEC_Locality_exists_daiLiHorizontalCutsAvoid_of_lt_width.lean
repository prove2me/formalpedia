-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiHorizontalCutsAvoid_of_lt_width
-- name    : QEC.Locality.exists_daiLiHorizontalCutsAvoid_of_lt_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:34.714104+00:00
-- url     : https://prove2.me/theorems/9ba3aba9-99e3-4951-9943-70375bc7aca0
-- title:
--   Locality: exists dai Li Horizontal Cuts Avoid of lt width
-- statement:
--   A strictly over-wide candidate band can be perturbed to two actual
--   support-free horizontal cuts while retaining the source separation scale.
--   This is the finite form of the final perturbation sentence in DL24's
--   plane-separator lemma; no cut is supplied by the caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1207-L1244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1207-L1244

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

theorem QEC.Locality.exists_daiLiHorizontalCutsAvoid_of_lt_width
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {candidateLower candidateUpper threshold : ℝ}
    (hThreshold : 0 ≤ threshold)
    (hWidth : threshold < candidateUpper - candidateLower) :
    ∃ lowerCut upperCut : ℝ,
      candidateLower < lowerCut ∧ lowerCut < candidateUpper ∧
      candidateLower < upperCut ∧ upperCut < candidateUpper ∧
      threshold < upperCut - lowerCut ∧
      DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut := by sorry
