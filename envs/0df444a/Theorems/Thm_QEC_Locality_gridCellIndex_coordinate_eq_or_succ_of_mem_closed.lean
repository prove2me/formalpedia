-- Prove2me | Theorems.Thm_QEC_Locality_gridCellIndex_coordinate_eq_or_succ_of_mem_closed
-- name    : QEC.Locality.gridCellIndex_coordinate_eq_or_succ_of_mem_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:02.697736+00:00
-- url     : https://prove2.me/theorems/4101b76c-a2d3-4c9a-a847-838013057ae6
-- title:
--   Locality: grid Cell Index coordinate eq or succ of mem closed
-- statement:
--   A qubit can lie in a closed cell only in one of the two adjacent integer
--   positions in each coordinate relative to its half-open owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L106-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L106-L130

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

theorem QEC.Locality.gridCellIndex_coordinate_eq_or_succ_of_mem_closed
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (origin : ℝ × ℝ) (cell : ℤ × ℤ) (q : ι)
    (hq : q ∈ daiLiGridCellClosedQubits embedding w origin cell) :
    (gridCellIndex w origin (embedding.point q)).1 = cell.1 ∨
      (gridCellIndex w origin (embedding.point q)).1 = cell.1 + 1 := by sorry
