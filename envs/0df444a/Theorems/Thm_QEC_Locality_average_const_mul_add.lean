-- Prove2me | Theorems.Thm_QEC_Locality_average_const_mul_add
-- name    : QEC.Locality.average_const_mul_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:01:37.702583+00:00
-- url     : https://prove2.me/theorems/c4b8eddd-5592-445c-b19e-d241afd50292
-- title:
--   Locality: average const mul add
-- statement:
--   The Locality construction uses the average const mul add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L408-L415
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L408-L415

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

theorem QEC.Locality.average_const_mul_add {a : Type*} [MeasurableSpace a]
    (mu : Measure a) (f g : a → ℝ) (A B : ℝ)
    (hf : Integrable f mu) (hg : Integrable g mu) :
    (⨍ x, B * f x + A * g x ∂mu) =
      B * (⨍ x, f x ∂mu) + A * (⨍ x, g x ∂mu) := by sorry
