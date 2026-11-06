-- Prove2me | Theorems.Thm_QEC_Locality_average_vertex_indicator
-- name    : QEC.Locality.average_vertex_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:00:49.144019+00:00
-- url     : https://prove2.me/theorems/d4d771e1-acc2-4832-a6d9-942be65c8838
-- title:
--   Locality: average vertex indicator
-- statement:
--   The Locality construction uses the average vertex indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L236-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L236-L259

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

theorem QEC.Locality.average_vertex_indicator (w ell : ℝ) [Fact (0 < w)]
    (hell : 0 ≤ ell) (hscale : 4 * ell ≤ w) (p : ℝ × ℝ) :
    (⨍ t : AddCircle w × AddCircle w,
      (if vertexBad w (2 * ell) t p then (1 : ℝ) else 0) ∂volume) =
      16 * ell ^ 2 / w ^ 2 := by sorry
