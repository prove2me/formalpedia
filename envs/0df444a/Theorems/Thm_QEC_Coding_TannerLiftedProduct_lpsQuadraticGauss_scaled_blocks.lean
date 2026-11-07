-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticGauss_scaled_blocks
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticGauss_scaled_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:37.012729+00:00
-- url     : https://prove2.me/theorems/a9b8134e-536c-4fb4-bb71-61a684115737
-- title:
--   Tanner Lifted Product: lps Quadratic Gauss scaled blocks
-- statement:
--   Each residue block contributes the same genuinely scaled quadratic sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L130-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L130-L146

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticGauss_scaled_blocks (d m : ℕ) [NeZero d] [NeZero m]
    (a : ℤ) :
    lpsUnaryQuadraticGauss (a*(d:ℤ)^2) (d*m) =
      (d:ℂ) * ∑ r : Fin m,
        ZMod.stdAddChar (((a*(d:ℤ)^2*(r.val:ℤ)^2):ℤ):ZMod (d*m)) := by sorry
