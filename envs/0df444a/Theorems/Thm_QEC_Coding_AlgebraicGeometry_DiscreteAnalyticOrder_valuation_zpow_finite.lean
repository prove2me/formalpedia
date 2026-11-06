-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_valuation_zpow_finite
-- name    : QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_zpow_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:02:43.265307+00:00
-- url     : https://prove2.me/theorems/5ceb594e-6fcb-4723-99ee-3bdaf1d8916e
-- title:
--   Discrete Analytic Order: valuation zpow finite
-- statement:
--   The same order formula holds for every integer power in the fraction field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L46-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L46-L55

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)

theorem QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_zpow_finite {f : K} {m : ℤ} (hf : v f = (m : WithTop ℤ)) (n : ℤ) :
    v (f ^ n) = (n * m : ℤ) := by sorry
