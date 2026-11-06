-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_valuation_pow_finite
-- name    : QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_pow_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:02:41.850323+00:00
-- url     : https://prove2.me/theorems/30f15912-ae19-4ee9-bbc8-56e980d2e4a2
-- title:
--   Discrete Analytic Order: valuation pow finite
-- statement:
--   The order of a natural power is the exponent times its finite order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L41-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L41-L43

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)

theorem QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_pow_finite {f : K} {m : ℤ} (hf : v f = (m : WithTop ℤ)) (n : ℕ) :
    v (f ^ n) = ((n : ℤ) * m : ℤ) := by sorry
