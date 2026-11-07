-- Prove2me | Theorems.Thm_QEC_Locality_gridCellQubits_subset_daiLiGridCellClosedQubits
-- name    : QEC.Locality.gridCellQubits_subset_daiLiGridCellClosedQubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:09:50.89168+00:00
-- url     : https://prove2.me/theorems/66d50675-7326-4ee4-97c7-a3dea1da8e22
-- title:
--   Locality: grid Cell Qubits subset dai Li Grid Cell Closed Qubits
-- statement:
--   Half-open ownership is contained in the closed physical witness square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L90-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L90-L96

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

theorem QEC.Locality.gridCellQubits_subset_daiLiGridCellClosedQubits
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (origin : ℝ × ℝ) (cell : ℤ × ℤ) :
    embedding.gridCellQubits w origin cell ⊆
      daiLiGridCellClosedQubits embedding w origin cell := by sorry
