-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_inflate
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_inflate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:47.487041+00:00
-- url     : https://prove2.me/theorems/3e328be4-0605-4b66-b2ce-12a5b0352e9a
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss inflate
-- statement:
--   Coefficient and modulus inflation repeat each actual lower-modulus phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L216-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L216-L245

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_inflate (m n : ℕ) [NeZero m] [NeZero n]
    (a : ℤ) :
    lpsUnaryQuadraticGauss (a*(m:ℤ)) (m*n) =
      (m:ℂ)*lpsUnaryQuadraticGauss a n := by sorry
