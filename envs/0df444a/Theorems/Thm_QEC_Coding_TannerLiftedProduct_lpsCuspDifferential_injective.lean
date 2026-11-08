-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspDifferential_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspDifferential_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:06.898263+00:00
-- url     : https://prove2.me/theorems/f6c40de8-3b29-45d0-a93a-c6530b73fcd0
-- title:
--   Tanner Lifted Product: lps Cusp Differential injective
-- statement:
--   Evaluation on the unit tangent proves that the original cusp form is recovered.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferential.lean#L28-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferential.lean#L28-L34

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspDifferential_injective (N : ℕ) :
    Function.Injective (lpsCuspDifferential N) := by sorry
