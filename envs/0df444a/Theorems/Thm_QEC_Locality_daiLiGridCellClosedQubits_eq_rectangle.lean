-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGridCellClosedQubits_eq_rectangle
-- name    : QEC.Locality.daiLiGridCellClosedQubits_eq_rectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:09:07.563756+00:00
-- url     : https://prove2.me/theorems/9578fab8-74a4-46b4-a386-b4dbb66247fd
-- title:
--   Locality: dai Li Grid Cell Closed Qubits eq rectangle
-- statement:
--   The closed witness square is exactly the expected closed rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L50-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L50-L87

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

theorem QEC.Locality.daiLiGridCellClosedQubits_eq_rectangle
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ)
    (cell : ℤ × ℤ) :
    daiLiGridCellClosedQubits embedding w origin cell =
      embedding.qubitsInRectangle (gridCellLower w origin cell)
        (gridCellUpper w origin cell) := by sorry
