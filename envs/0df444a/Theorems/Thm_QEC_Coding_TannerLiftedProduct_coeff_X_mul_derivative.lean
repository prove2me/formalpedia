-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_X_mul_derivative
-- name    : QEC.Coding.TannerLiftedProduct.coeff_X_mul_derivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:52:11.228717+00:00
-- url     : https://prove2.me/theorems/66930615-4ec3-4763-ad4f-83f1cb0e4d99
-- title:
--   Tanner Lifted Product: coeff X mul derivative
-- statement:
--   Multiplication by `X` restores the degree dropped by differentiation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L104-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L104-L113

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.coeff_X_mul_derivative (f : ℚ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative ℚ f) =
      (n : ℚ) * PowerSeries.coeff n f := by sorry
