-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_square_modulus
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_square_modulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:41.983975+00:00
-- url     : https://prove2.me/theorems/45c3aa86-3cf2-4d6c-b011-1b299b9dd267
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss square modulus
-- statement:
--   Square scaling and inflation remove a square factor from the actual modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L248-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L248-L264

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_square_modulus (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (a b u : ℤ) (hdet : a*u-b*((4*d^2*k:ℕ):ℤ)=1) :
    lpsUnaryQuadraticGauss a (4*d^2*k) =
      (d:ℂ)*lpsUnaryQuadraticGauss a (4*k) := by sorry
