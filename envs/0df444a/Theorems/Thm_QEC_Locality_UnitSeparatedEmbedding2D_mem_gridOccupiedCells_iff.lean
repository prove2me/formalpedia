-- Prove2me | Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
-- name    : QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:47:48.417842+00:00
-- url     : https://prove2.me/theorems/96149936-b041-4919-bb67-07cf02b1953f
-- title:
--   Unit Separated Embedding2 D: mem grid Occupied Cells iff
-- statement:
--   The Unit Separated Embedding2 D construction uses the mem grid Occupied Cells iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L118-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L118-L123

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

theorem QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) :
    cell ∈ embedding.gridOccupiedCells w origin ↔
      ∃ q : ι, gridCellIndex w origin (embedding.point q) = cell := by sorry
