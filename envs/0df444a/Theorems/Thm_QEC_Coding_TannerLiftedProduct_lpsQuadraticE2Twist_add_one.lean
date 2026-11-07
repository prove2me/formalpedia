-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_add_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:20.216318+00:00
-- url     : https://prove2.me/theorems/d67f4d24-f358-497f-ac96-2ce4b45430f0
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist add one
-- statement:
--   The actual twist inherits period one from each E2 translate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L205-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L205-L213

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_add_one (q : ℕ) [Fact q.Prime] (z : ℍ) :
    lpsQuadraticE2Twist q ((1:ℝ) +ᵥ z)=lpsQuadraticE2Twist q z := by sorry
