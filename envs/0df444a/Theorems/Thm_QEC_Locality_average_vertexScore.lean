-- Prove2me | Theorems.Thm_QEC_Locality_average_vertexScore
-- name    : QEC.Locality.average_vertexScore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:48:50.032227+00:00
-- url     : https://prove2.me/theorems/29003230-e287-4066-bf07-0bc7fa7e7c8b
-- title:
--   Locality: average vertex Score
-- statement:
--   The Locality construction uses the average vertex Score property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L358-L381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L358-L381

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

theorem QEC.Locality.average_vertexScore {a : Type*} [Fintype a] (w ell : ℝ) [Fact (0 < w)]
    (hell : 0 ≤ ell) (hscale : 4 * ell ≤ w) (points : a → ℝ × ℝ) :
    (⨍ t, vertexScore w (2 * ell) points t ∂volume) =
      Fintype.card a * (16 * ell ^ 2 / w ^ 2) := by sorry
