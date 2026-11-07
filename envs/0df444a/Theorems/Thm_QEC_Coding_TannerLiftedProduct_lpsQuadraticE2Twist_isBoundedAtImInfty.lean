-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_isBoundedAtImInfty
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_isBoundedAtImInfty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:09.294953+00:00
-- url     : https://prove2.me/theorems/45a4d92a-cc9a-4156-81e6-a99ad321f352
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist is Bounded At Im Infty
-- statement:
--   The genuine convergent series supplies boundedness in the full infinity filter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L190-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L190-L194

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_isBoundedAtImInfty (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    UpperHalfPlane.IsBoundedAtImInfty (fun z : ℍ => lpsQuadraticE2Twist q z) := by sorry
