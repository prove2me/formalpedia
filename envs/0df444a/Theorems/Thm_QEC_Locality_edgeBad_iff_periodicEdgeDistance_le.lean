-- Prove2me | Theorems.Thm_QEC_Locality_edgeBad_iff_periodicEdgeDistance_le
-- name    : QEC.Locality.edgeBad_iff_periodicEdgeDistance_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:37:20.113834+00:00
-- url     : https://prove2.me/theorems/323bdf1e-dfde-40f2-a833-fdc1b79624d7
-- title:
--   Locality: edge Bad iff periodic Edge Distance le
-- statement:
--   The Locality construction uses the edge Bad iff periodic Edge Distance le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L202-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L202-L205

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

theorem QEC.Locality.edgeBad_iff_periodicEdgeDistance_le
    (w r : ℝ) (t : GridTranslation w) (p : ℝ × ℝ) :
    edgeBad w r t p ↔ periodicEdgeDistance w t p ≤ r := by sorry
