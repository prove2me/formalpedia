-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwo_slash_deriv
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwo_slash_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:00.676654+00:00
-- url     : https://prove2.me/theorems/4505404e-e51d-4e3a-8060-445dd33b451e
-- title:
--   Tanner Lifted Product: lps Weight Two slash deriv
-- statement:
--   Positive determinant weight-two slash is actual holomorphic differential pullback.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferential.lean#L37-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferential.lean#L37-L46

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwo_slash_deriv (f : ℍ→ℂ) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) (τ : ℍ) :
    (f ∣[(2:ℤ)] g) τ = f (g • τ)*
      deriv (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ := by sorry
