-- Prove2me | Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_self
-- name    : QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:00:42.826735+00:00
-- url     : https://prove2.me/theorems/5bdb7b32-c9c9-4754-8e74-3f8a74ffe43a
-- title:
--   Unit Separated Embedding2 D: mem grid Cell Qubits self
-- statement:
--   Every qubit is assigned to its concrete grid cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L126-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L126-L131

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

theorem QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_self {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (q : ι) :
    q ∈ embedding.gridCellQubits w origin
      (gridCellIndex w origin (embedding.point q)) := by sorry
