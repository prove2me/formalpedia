-- Prove2me | Theorems.Thm_QEC_Locality_measurableSet_packingBox
-- name    : QEC.Locality.measurableSet_packingBox
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:01:55.624118+00:00
-- url     : https://prove2.me/theorems/171785bc-39a6-4d54-a9b6-651559caaa74
-- title:
--   Locality: measurable Set packing Box
-- statement:
--   The Locality construction uses the measurable Set packing Box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L631-L632
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L631-L632

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

theorem QEC.Locality.measurableSet_packingBox (p : ℝ × ℝ) : MeasurableSet (packingBox p) := by sorry
