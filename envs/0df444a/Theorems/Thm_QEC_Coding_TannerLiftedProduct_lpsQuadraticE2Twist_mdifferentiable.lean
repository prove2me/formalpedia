-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_mdifferentiable
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_mdifferentiable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:02.399987+00:00
-- url     : https://prove2.me/theorems/a1419fd5-0b7d-4f28-b22c-153ef63c64cb
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist mdifferentiable
-- statement:
--   The actual finite weighted sum is holomorphic on the upper half plane.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L175-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L175-L187

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_mdifferentiable (q : ℕ) [Fact q.Prime] :
    MDiff (fun z : ℍ => lpsQuadraticE2Twist q z) := by sorry
