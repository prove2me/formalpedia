-- Prove2me | Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
-- name    : QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:47:44.013101+00:00
-- url     : https://prove2.me/theorems/2768c450-715a-469f-a669-2afae6fcd50c
-- title:
--   Unit Separated Embedding2 D: mem qubits In Rectangle iff
-- statement:
--   The Unit Separated Embedding2 D construction uses the mem qubits In Rectangle iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L974-L978
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L974-L978

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

theorem QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
    {i : Type*} [Fintype i] [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (lower upper : ℝ × ℝ) (p : i) :
    p ∈ embedding.qubitsInRectangle lower upper ↔ embedding.point p ∈ rectangle lower upper := by sorry
