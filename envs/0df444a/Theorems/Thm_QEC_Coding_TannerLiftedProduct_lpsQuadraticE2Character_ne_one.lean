-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_ne_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:01.438405+00:00
-- url     : https://prove2.me/theorems/b5dd14ec-96b8-4622-89a8-df02da10e965
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Character ne one
-- statement:
--   The odd-prime quadratic character is genuinely nontrivial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L83-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L83-L88

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_ne_one (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    lpsQuadraticE2Character q≠1 := by sorry
