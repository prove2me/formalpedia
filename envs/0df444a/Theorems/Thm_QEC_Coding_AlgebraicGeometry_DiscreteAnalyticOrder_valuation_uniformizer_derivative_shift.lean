-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_valuation_uniformizer_derivative_shift
-- name    : QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_uniformizer_derivative_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:04:36.148077+00:00
-- url     : https://prove2.me/theorems/6dd816e2-45c0-4c16-8229-edb7e363c00a
-- title:
--   Discrete Analytic Order: valuation uniformizer derivative shift
-- statement:
--   The derivative shift by the positive uniformizer order preserves the field no-pole criterion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L85-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L85-L91

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)

theorem QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_uniformizer_derivative_shift [IsDiscreteValuationRing V]
    (π : V) (hπ : Irreducible π) {m : ℤ}
    (hpos : 0 < m) (hm : v (π : K) = (m : WithTop ℤ)) {f : K} (hf : f ≠ 0) :
    0 ≤ v f + ((m - 1 : ℤ) : WithTop ℤ) ↔ 0 ≤ v f := by sorry
