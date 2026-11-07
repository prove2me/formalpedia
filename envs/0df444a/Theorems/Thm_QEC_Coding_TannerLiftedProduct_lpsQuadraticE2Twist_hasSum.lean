-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:53.639825+00:00
-- url     : https://prove2.me/theorems/05df5751-a1b8-4f37-bb51-5fe91bce1276
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist has Sum
-- statement:
--   Finite Fourier summation computes the convergent divisor series of the actual twist.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L116-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L116-L143

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_hasSum (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ) *
      lpsQuadraticE2Character q (n:ZMod q) * Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsQuadraticE2Twist q z) := by sorry
