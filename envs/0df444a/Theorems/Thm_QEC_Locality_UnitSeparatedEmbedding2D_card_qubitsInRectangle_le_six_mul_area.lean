-- Prove2me | Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_card_qubitsInRectangle_le_six_mul_area
-- name    : QEC.Locality.UnitSeparatedEmbedding2D.card_qubitsInRectangle_le_six_mul_area
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:48:02.314345+00:00
-- url     : https://prove2.me/theorems/11e34398-7482-4a14-816e-410f502495ef
-- title:
--   Unit Separated Embedding2 D: card qubits In Rectangle le six mul area
-- statement:
--   Downstream-ready form of the two-dimensional rectangle packing bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L981-L990
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L981-L990

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

theorem QEC.Locality.UnitSeparatedEmbedding2D.card_qubitsInRectangle_le_six_mul_area
    {i : Type*} [Fintype i] [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (lower upper : ℝ × ℝ)
    (hwidth : 1 ≤ upper.1 - lower.1) (hheight : 1 ≤ upper.2 - lower.2) :
    ((embedding.qubitsInRectangle lower upper).card : ℝ) ≤
      6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) := by sorry
