-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_uniformizer_order_positive
-- name    : QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.uniformizer_order_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:02:34.846403+00:00
-- url     : https://prove2.me/theorems/58ba3c3f-9c28-4aa4-90a5-2acdc28e4db6
-- title:
--   Discrete Analytic Order: uniformizer order positive
-- statement:
--   An irreducible valuation-ring element has strictly positive additive order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L23-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L23-L25

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)

theorem QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.uniformizer_order_positive (π : V) (hπ : Irreducible π) :
    0 < v (π : K) := by sorry
