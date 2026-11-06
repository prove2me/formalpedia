-- Prove2me | Theorems.Thm_QEC_Locality_measurableSet_vertexBad
-- name    : QEC.Locality.measurableSet_vertexBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:48:00.881812+00:00
-- url     : https://prove2.me/theorems/783c9783-2205-4645-b187-aa499344147c
-- title:
--   Locality: measurable Set vertex Bad
-- statement:
--   The Locality construction uses the measurable Set vertex Bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L180-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L180-L183

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

theorem QEC.Locality.measurableSet_vertexBad (w r : ℝ) (p : ℝ × ℝ) :
    MeasurableSet {t : AddCircle w × AddCircle w | vertexBad w r t p} := by sorry
