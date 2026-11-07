-- Prove2me | Theorems.Thm_QEC_Locality_gridCellIndex_coordinate_eq_or_succ_of_mem_closed_y
-- name    : QEC.Locality.gridCellIndex_coordinate_eq_or_succ_of_mem_closed_y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:23.27059+00:00
-- url     : https://prove2.me/theorems/98793784-65ef-4ffa-87b9-a884051ae8e1
-- title:
--   Locality: grid Cell Index coordinate eq or succ of mem closed y
-- statement:
--   The Locality construction uses the grid Cell Index coordinate eq or succ of mem closed y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L132-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L132-L156

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

theorem QEC.Locality.gridCellIndex_coordinate_eq_or_succ_of_mem_closed_y
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (origin : ℝ × ℝ) (cell : ℤ × ℤ) (q : ι)
    (hq : q ∈ daiLiGridCellClosedQubits embedding w origin cell) :
    (gridCellIndex w origin (embedding.point q)).2 = cell.2 ∨
      (gridCellIndex w origin (embedding.point q)).2 = cell.2 + 1 := by sorry
