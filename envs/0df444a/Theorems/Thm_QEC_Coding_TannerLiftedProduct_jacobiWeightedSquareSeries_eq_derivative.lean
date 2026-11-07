-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiWeightedSquareSeries_eq_derivative
-- name    : QEC.Coding.TannerLiftedProduct.jacobiWeightedSquareSeries_eq_derivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:56:48.253419+00:00
-- url     : https://prove2.me/theorems/4958026c-58ca-4c67-a230-9227783fe963
-- title:
--   Tanner Lifted Product: jacobi Weighted Square Series eq derivative
-- statement:
--   The square weight identity `(2z)² = 4z²` similarly says that the
--   weighted square series is `4X` times the derivative of the theta series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L142-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L142-L160

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.jacobiWeightedSquareSeries_eq_derivative :
    jacobiWeightedSquareSeries =
      PowerSeries.C 4 *
        (PowerSeries.X *
          PowerSeries.derivative ℚ rationalIntegerThetaSeries) := by sorry
