-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_valuationUnit_order
-- name    : QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuationUnit_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:02:22.383091+00:00
-- url     : https://prove2.me/theorems/84268d6a-9df3-4b72-bf1d-8fd734284321
-- title:
--   Discrete Analytic Order: valuation Unit order
-- statement:
--   A unit of the valuation ring has additive order zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L19-L20
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L19-L20

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)

theorem QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuationUnit_order (u : Vˣ) : v ((u : V) : K) = 0 := by sorry
