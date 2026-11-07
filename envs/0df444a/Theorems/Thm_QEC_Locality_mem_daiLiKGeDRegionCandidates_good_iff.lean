-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCandidates_good_iff
-- name    : QEC.Locality.mem_daiLiKGeDRegionCandidates_good_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:09:31.424809+00:00
-- url     : https://prove2.me/theorems/0fc1b49c-d93d-402c-b035-301a497b50c8
-- title:
--   Locality: mem dai Li KGe DRegion Candidates good iff
-- statement:
--   A grid-cell index is present exactly when that occupied cell is not
--   classified bad.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2299-L2308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2299-L2308

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

theorem QEC.Locality.mem_daiLiKGeDRegionCandidates_good_iff
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) (cell : ℤ × ℤ) :
    Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d w origin rectangles ↔
      cell ∈ embedding.gridOccupiedCells w origin ∧
        cell ∉ daiLiBadGridCells P embedding threshold d w origin := by sorry
