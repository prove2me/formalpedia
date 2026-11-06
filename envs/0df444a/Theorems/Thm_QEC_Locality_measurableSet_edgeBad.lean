-- Prove2me | Theorems.Thm_QEC_Locality_measurableSet_edgeBad
-- name    : QEC.Locality.measurableSet_edgeBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:48:15.710615+00:00
-- url     : https://prove2.me/theorems/7d2c6250-15ea-4887-8ab9-d5fd54ecb56d
-- title:
--   Locality: measurable Set edge Bad
-- statement:
--   The Locality construction uses the measurable Set edge Bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L214-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L214-L218

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

theorem QEC.Locality.measurableSet_edgeBad (w r : ℝ) (p : ℝ × ℝ) :
    MeasurableSet {t : AddCircle w × AddCircle w | edgeBad w r t p} := by sorry
