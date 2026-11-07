-- Prove2me | Theorems.Thm_QEC_Locality_daiLiBadGridCellSubdivision_empty_or_total_lower
-- name    : QEC.Locality.daiLiBadGridCellSubdivision_empty_or_total_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:14:49.494288+00:00
-- url     : https://prove2.me/theorems/9ead6164-aa5e-4867-8583-9f676de3cbcf
-- title:
--   Locality: dai Li Bad Grid Cell Subdivision empty or total lower
-- statement:
--   A nonempty constructed bad-grid subdivision carries the exact bad-square
--   counter lower bound needed for its integer count handoff.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L925-L937
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L925-L937

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

theorem QEC.Locality.daiLiBadGridCellSubdivision_empty_or_total_lower
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    (∑ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      (rectangles cell).length) = 0 ∨
      d ≤ 10 * daiLiBadGridTotalF P embedding threshold d w origin := by sorry
