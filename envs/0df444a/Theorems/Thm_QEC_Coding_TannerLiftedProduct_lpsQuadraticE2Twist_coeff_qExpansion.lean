-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_coeff_qExpansion
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_coeff_qExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:25.742607+00:00
-- url     : https://prove2.me/theorems/0ba10320-93ce-4dd3-9c3e-c7be9f101c5b
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist coeff q Expansion
-- statement:
--   The actual analytic q-expansion has the proved character-weighted divisor coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L234-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L234-L244

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_coeff_qExpansion (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (fun z : ℍ => lpsQuadraticE2Twist q z)) =
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q) := by sorry
