-- Prove2me | Theorems.Thm_QEC_Locality_vertexScore_eq_cast_count
-- name    : QEC.Locality.vertexScore_eq_cast_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:48:46.24719+00:00
-- url     : https://prove2.me/theorems/d3841cf5-92f4-4007-9561-5ea4fa1881aa
-- title:
--   Locality: vertex Score eq cast count
-- statement:
--   The Locality construction uses the vertex Score eq cast count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L322-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L322-L325

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

theorem QEC.Locality.vertexScore_eq_cast_count {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) :
    vertexScore w r points t = (vertexBadCount w r points t : ℝ) := by sorry
