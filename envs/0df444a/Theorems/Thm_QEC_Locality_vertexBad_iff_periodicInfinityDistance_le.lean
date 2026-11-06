-- Prove2me | Theorems.Thm_QEC_Locality_vertexBad_iff_periodicInfinityDistance_le
-- name    : QEC.Locality.vertexBad_iff_periodicInfinityDistance_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:36:39.514084+00:00
-- url     : https://prove2.me/theorems/9a3786a1-3b3a-4b0c-95a3-548856609f49
-- title:
--   Locality: vertex Bad iff periodic Infinity Distance le
-- statement:
--   The Locality construction uses the vertex Bad iff periodic Infinity Distance le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L175-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L175-L178

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

theorem QEC.Locality.vertexBad_iff_periodicInfinityDistance_le
    (w r : ℝ) (t : GridTranslation w) (p : ℝ × ℝ) :
    vertexBad w r t p ↔ periodicInfinityDistance w t p ≤ r := by sorry
