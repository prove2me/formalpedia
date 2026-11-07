-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeDRegionCandidate_host_occupied
-- name    : QEC.Locality.daiLiKGeDRegionCandidate_host_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:19:03.254403+00:00
-- url     : https://prove2.me/theorems/87af098d-cd08-4812-b56d-3082b2d298c1
-- title:
--   Locality: dai Li KGe DRegion Candidate host occupied
-- statement:
--   Every finite source-region candidate is rooted in an occupied physical
--   grid cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2348-L2364
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2348-L2364

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

theorem QEC.Locality.daiLiKGeDRegionCandidate_host_occupied
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex)
    (hRegion : region ∈ daiLiKGeDRegionCandidates P embedding threshold d w origin rectangles) :
    daiLiKGeDRegionHostCell region ∈ embedding.gridOccupiedCells w origin := by sorry
