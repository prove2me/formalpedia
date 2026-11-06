-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_valuation_eq_multiple_uniformizer
-- name    : QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_eq_multiple_uniformizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:02:45.611806+00:00
-- url     : https://prove2.me/theorems/0c13d897-937f-4d3f-a78e-39179bbe4116
-- title:
--   Discrete Analytic Order: valuation eq multiple uniformizer
-- statement:
--   DVR factorization makes every nonzero field order an integer multiple of uniformizer order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L58-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L58-L66

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)

theorem QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_eq_multiple_uniformizer [IsDiscreteValuationRing V]
    (π : V) (hπ : Irreducible π) {m : ℤ} (hm : v (π : K) = (m : WithTop ℤ))
    {f : K} (hf : f ≠ 0) : ∃ n : ℤ, v f = (n * m : ℤ) := by sorry
