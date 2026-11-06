-- Prove2me | Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_gridCellQubits_cover
-- name    : QEC.Locality.UnitSeparatedEmbedding2D.gridCellQubits_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:36:38.569371+00:00
-- url     : https://prove2.me/theorems/f5b7054e-9b6c-47ad-ac8c-67f22dd548d1
-- title:
--   Unit Separated Embedding2 D: grid Cell Qubits cover
-- statement:
--   The occupied finite cell family covers every qubit exactly once.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L149-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L149-L161

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable

theorem QEC.Locality.UnitSeparatedEmbedding2D.gridCellQubits_cover {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) :
    (embedding.gridOccupiedCells w origin).biUnion
      (embedding.gridCellQubits w origin) = Finset.univ := by sorry
