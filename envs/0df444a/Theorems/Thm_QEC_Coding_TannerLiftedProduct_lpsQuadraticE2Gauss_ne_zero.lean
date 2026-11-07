-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Gauss_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Gauss_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:14.229213+00:00
-- url     : https://prove2.me/theorems/208210c2-1bef-4a49-868b-ac281e8432cd
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Gauss ne zero
-- statement:
--   The actual primitive character Gauss sum supplies a valid normalization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L91-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L91-L97

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Gauss_ne_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))≠0 := by sorry
