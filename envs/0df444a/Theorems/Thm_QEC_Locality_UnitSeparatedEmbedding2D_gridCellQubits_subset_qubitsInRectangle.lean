-- Prove2me | Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_gridCellQubits_subset_qubitsInRectangle
-- name    : QEC.Locality.UnitSeparatedEmbedding2D.gridCellQubits_subset_qubitsInRectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:38:38.880799+00:00
-- url     : https://prove2.me/theorems/12a8dcb2-361c-47b2-b07c-20aa406637cb
-- title:
--   Unit Separated Embedding2 D: grid Cell Qubits subset qubits In Rectangle
-- statement:
--   A half-open cell is contained in its corresponding closed geometric
--   rectangle, which is the form consumed by the existing packing estimates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L994-L1034
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L994-L1034

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

theorem QEC.Locality.UnitSeparatedEmbedding2D.gridCellQubits_subset_qubitsInRectangle
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (origin : ℝ × ℝ) (cell : ℤ × ℤ) :
    embedding.gridCellQubits w origin cell ⊆
      embedding.qubitsInRectangle (gridCellLower w origin cell)
        (gridCellUpper w origin cell) := by sorry
