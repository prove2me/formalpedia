-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_real_shift_mdifferentiable
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2_real_shift_mdifferentiable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:05.573758+00:00
-- url     : https://prove2.me/theorems/d52d5e57-5350-4433-bda2-039d605bf133
-- title:
--   Tanner Lifted Product: lps E2 real shift mdifferentiable
-- statement:
--   Actual E2 holomorphicity is preserved under the real translation action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L157-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L157-L172

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2_real_shift_mdifferentiable (r : ℝ) :
    MDiff (fun z : ℍ => EisensteinSeries.E2 (r +ᵥ z)) := by sorry
