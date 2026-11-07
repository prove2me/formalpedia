-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCandidates_bad_iff
-- name    : QEC.Locality.mem_daiLiKGeDRegionCandidates_bad_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:09:11.253034+00:00
-- url     : https://prove2.me/theorems/c20422f3-905e-4fa2-bcdd-8d5c9516fae8
-- title:
--   Locality: mem dai Li KGe DRegion Candidates bad iff
-- statement:
--   A rectangle index is present exactly when it names a position of the
--   concrete list belonging to an actual bad grid cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2312-L2322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2312-L2322

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

theorem QEC.Locality.mem_daiLiKGeDRegionCandidates_bad_iff
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) :
    Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d w origin rectangles ↔
      cell ∈ daiLiBadGridCells P embedding threshold d w origin ∧
        slot < (rectangles cell).length := by sorry
