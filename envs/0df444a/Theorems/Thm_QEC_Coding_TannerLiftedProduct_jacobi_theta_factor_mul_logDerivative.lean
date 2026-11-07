-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_theta_factor_mul_logDerivative
-- name    : QEC.Coding.TannerLiftedProduct.jacobi_theta_factor_mul_logDerivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:31.337905+00:00
-- url     : https://prove2.me/theorems/3d6a06a4-8ead-4d6c-9475-7fe46822a964
-- title:
--   Tanner Lifted Product: jacobi theta factor mul log Derivative
-- statement:
--   The supplied logarithmic derivative is correct for every combined
--   theta-product factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L206-L221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L206-L221

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.jacobi_theta_factor_mul_logDerivative (n : ℕ) :
    (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) *
      jacobiThetaLogDerivativeSummand n =
    PowerSeries.derivative ℚ
      (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) := by sorry
