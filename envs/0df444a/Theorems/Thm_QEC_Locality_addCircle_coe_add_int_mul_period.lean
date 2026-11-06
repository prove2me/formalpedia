-- Prove2me | Theorems.Thm_QEC_Locality_addCircle_coe_add_int_mul_period
-- name    : QEC.Locality.addCircle_coe_add_int_mul_period
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:34:38.80485+00:00
-- url     : https://prove2.me/theorems/78d181d8-9cfc-4780-b7f9-9645c01cd00d
-- title:
--   Locality: add Circle coe add int mul period
-- statement:
--   Translating a real representative by an integral number of periods does
--   not change its point on the quotient circle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L77-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L77-L83

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

theorem QEC.Locality.addCircle_coe_add_int_mul_period (w x : ℝ) (m : ℤ) :
    ((x + (m : ℝ) * w : ℝ) : AddCircle w) = (x : AddCircle w) := by sorry
