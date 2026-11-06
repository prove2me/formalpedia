-- Prove2me | Theorems.Thm_QEC_Locality_vertexBad_set
-- name    : QEC.Locality.vertexBad_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:00:50.291498+00:00
-- url     : https://prove2.me/theorems/bb75890c-f4c2-448f-a3c9-7371458cb430
-- title:
--   Locality: vertex Bad set
-- statement:
--   The Locality construction uses the vertex Bad set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L185-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L185-L189

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

theorem QEC.Locality.vertexBad_set (w r : ℝ) (p : ℝ × ℝ) :
    {t : AddCircle w × AddCircle w | vertexBad w r t p} =
      closedBall (phase w p).1 r ×ˢ closedBall (phase w p).2 r := by sorry
