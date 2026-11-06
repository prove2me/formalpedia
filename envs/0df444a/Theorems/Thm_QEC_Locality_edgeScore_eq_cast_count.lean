-- Prove2me | Theorems.Thm_QEC_Locality_edgeScore_eq_cast_count
-- name    : QEC.Locality.edgeScore_eq_cast_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:48:22.114343+00:00
-- url     : https://prove2.me/theorems/67dbd05b-98f9-405e-b68d-2b4ceb99e2a2
-- title:
--   Locality: edge Score eq cast count
-- statement:
--   The Locality construction uses the edge Score eq cast count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L327-L330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L327-L330

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

theorem QEC.Locality.edgeScore_eq_cast_count {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) :
    edgeScore w r points t = (edgeBadCount w r points t : ℝ) := by sorry
