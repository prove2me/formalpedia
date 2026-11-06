-- Prove2me | Theorems.Thm_QEC_Locality_measure_edgeBad_le
-- name    : QEC.Locality.measure_edgeBad_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:00:43.708802+00:00
-- url     : https://prove2.me/theorems/6301d8b5-bf67-4c54-a62f-7e6e7bd709c4
-- title:
--   Locality: measure edge Bad le
-- statement:
--   The Locality construction uses the measure edge Bad le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L220-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L220-L234

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

theorem QEC.Locality.measure_edgeBad_le (w r : ℝ) [Fact (0 < w)] (p : ℝ × ℝ) :
    volume {t : AddCircle w × AddCircle w | edgeBad w r t p} ≤
      2 * (ENNReal.ofReal (min w (2 * r)) * ENNReal.ofReal w) := by sorry
