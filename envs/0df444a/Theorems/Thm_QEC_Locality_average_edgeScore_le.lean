-- Prove2me | Theorems.Thm_QEC_Locality_average_edgeScore_le
-- name    : QEC.Locality.average_edgeScore_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:49:27.544761+00:00
-- url     : https://prove2.me/theorems/5893d360-7beb-4b6e-8593-4e3b5a845d4b
-- title:
--   Locality: average edge Score le
-- statement:
--   The Locality construction uses the average edge Score le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L383-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L383-L406

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

theorem QEC.Locality.average_edgeScore_le {a : Type*} [Fintype a] (w ell : ℝ) [Fact (0 < w)]
    (hell : 0 ≤ ell) (hscale : 4 * ell ≤ w) (points : a → ℝ × ℝ) :
    (⨍ t, edgeScore w (2 * ell) points t ∂volume) ≤
      Fintype.card a * (8 * ell / w) := by sorry
