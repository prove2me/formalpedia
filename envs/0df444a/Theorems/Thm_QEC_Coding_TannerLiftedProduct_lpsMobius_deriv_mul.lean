-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsMobius_deriv_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsMobius_deriv_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:46:08.632195+00:00
-- url     : https://prove2.me/theorems/348115a5-e37e-42d1-bad4-83f98a12bc19
-- title:
--   Tanner Lifted Product: lps Mobius deriv mul
-- statement:
--   The derivative of a positive-determinant Mobius product satisfies the actual chain rule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L96-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L96-L112

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsMobius_deriv_mul (r g : GL (Fin 2) ℝ)
    (hr : 0<r.val.det) (hg : 0<g.val.det) (τ : ℍ) :
    deriv (fun z : ℂ => ((r*g) • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ=
      deriv (fun z : ℂ => (r • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) (g • τ : ℍ) *
      deriv (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ := by sorry
