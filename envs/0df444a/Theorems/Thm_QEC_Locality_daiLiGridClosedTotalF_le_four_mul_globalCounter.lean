-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGridClosedTotalF_le_four_mul_globalCounter
-- name    : QEC.Locality.daiLiGridClosedTotalF_le_four_mul_globalCounter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:34.139449+00:00
-- url     : https://prove2.me/theorems/290adcae-97b6-4875-b4ea-6ef2433e0577
-- title:
--   Locality: dai Li Grid Closed Total F le four mul global Counter
-- statement:
--   The closed-cell incidence total is at most four times the actual global
--   long-incidence total.  The factor is an exact finite boundary-overlap charge,
--   not an assumption that a periodic tiling has no boundary qubits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L278-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L278-L317

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable

theorem QEC.Locality.daiLiGridClosedTotalF_le_four_mul_globalCounter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) {w : ℝ}
    (hw : 0 < w) (origin : ℝ × ℝ) :
    daiLiGridClosedTotalF P embedding threshold w origin ≤
      4 * ∑ q : ι, P.daiLiInteractionCounter embedding threshold q := by sorry
