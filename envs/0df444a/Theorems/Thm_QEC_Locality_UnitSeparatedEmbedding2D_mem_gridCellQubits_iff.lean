-- Prove2me | Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
-- name    : QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:47:50.225056+00:00
-- url     : https://prove2.me/theorems/35296001-0718-4874-9fb8-a6a221a5a21c
-- title:
--   Unit Separated Embedding2 D: mem grid Cell Qubits iff
-- statement:
--   The Unit Separated Embedding2 D construction uses the mem grid Cell Qubits iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L110-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L110-L115

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

theorem QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) (q : ι) :
    q ∈ embedding.gridCellQubits w origin cell ↔
      gridCellIndex w origin (embedding.point q) = cell := by sorry
