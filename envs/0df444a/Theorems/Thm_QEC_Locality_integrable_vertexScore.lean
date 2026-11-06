-- Prove2me | Theorems.Thm_QEC_Locality_integrable_vertexScore
-- name    : QEC.Locality.integrable_vertexScore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:48:20.909004+00:00
-- url     : https://prove2.me/theorems/493a6530-63e3-4b37-8003-2b64ca24142a
-- title:
--   Locality: integrable vertex Score
-- statement:
--   The Locality construction uses the integrable vertex Score property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L332-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L332-L343

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

theorem QEC.Locality.integrable_vertexScore {a : Type*} [Fintype a] (w r : ℝ) [Fact (0 < w)]
    (points : a → ℝ × ℝ) : Integrable (vertexScore w r points) volume := by sorry
