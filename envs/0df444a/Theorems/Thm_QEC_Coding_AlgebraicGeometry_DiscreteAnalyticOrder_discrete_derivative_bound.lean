-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_discrete_derivative_bound
-- name    : QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.discrete_derivative_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:02:52.462201+00:00
-- url     : https://prove2.me/theorems/55198552-ebf4-4a71-8ba1-3ef7853c1949
-- title:
--   Discrete Analytic Order: discrete derivative bound
-- statement:
--   The discrete order gap detects nonnegativity even after adding the derivative shift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L69-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L69-L82

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)

theorem QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.discrete_derivative_bound {n m : ℤ} (hm : 0 < m) :
    0 ≤ n * m + (m - 1) ↔ 0 ≤ n * m := by sorry
