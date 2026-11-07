-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_square_scale
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_square_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:45.733012+00:00
-- url     : https://prove2.me/theorems/8f291bf5-cd24-4c63-b8bb-d7724a273d00
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss square scale
-- statement:
--   Perfect-square scaling follows from the actual mask projection and completed square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L194-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L194-L213

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_square_scale (N d k : ℕ) [NeZero N]
    (hN : N=4*d^2*k) (hd : 0 < d) (hk : 0 < k)
    (a b u : ℤ) (hdet : a*u-b*(N:ℤ)=1) :
    lpsUnaryQuadraticGauss (a*(d:ℤ)^2) N =
      (d:ℂ)*lpsUnaryQuadraticGauss a N := by sorry
