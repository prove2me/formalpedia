-- Prove2me | Theorems.Thm_QEC_Locality_integrable_edgeScore
-- name    : QEC.Locality.integrable_edgeScore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:49:11.028415+00:00
-- url     : https://prove2.me/theorems/0b9c43b2-0a7c-4bb6-9e36-6a34147cb033
-- title:
--   Locality: integrable edge Score
-- statement:
--   The Locality construction uses the integrable edge Score property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L345-L356
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L345-L356

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

theorem QEC.Locality.integrable_edgeScore {a : Type*} [Fintype a] (w r : ℝ) [Fact (0 < w)]
    (points : a → ℝ × ℝ) : Integrable (edgeScore w r points) volume := by sorry
