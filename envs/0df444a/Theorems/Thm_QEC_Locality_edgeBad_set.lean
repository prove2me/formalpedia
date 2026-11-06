-- Prove2me | Theorems.Thm_QEC_Locality_edgeBad_set
-- name    : QEC.Locality.edgeBad_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:48:31.82023+00:00
-- url     : https://prove2.me/theorems/784c79b5-2269-4a39-ad22-93fff4f913ae
-- title:
--   Locality: edge Bad set
-- statement:
--   The Locality construction uses the edge Bad set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L207-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L207-L212

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

theorem QEC.Locality.edgeBad_set (w r : ℝ) (p : ℝ × ℝ) :
    {t : AddCircle w × AddCircle w | edgeBad w r t p} =
      (closedBall (phase w p).1 r ×ˢ Set.univ) ∪
        (Set.univ ×ˢ closedBall (phase w p).2 r) := by sorry
