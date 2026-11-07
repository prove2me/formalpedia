-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_triangular_factor_mul_logDerivative
-- name    : QEC.Coding.TannerLiftedProduct.jacobi_triangular_factor_mul_logDerivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:55.594587+00:00
-- url     : https://prove2.me/theorems/20da3f63-b6d1-4e22-91dc-996969c94f49
-- title:
--   Tanner Lifted Product: jacobi triangular factor mul log Derivative
-- statement:
--   The supplied logarithmic derivative is correct for every combined
--   triangular-product factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L249-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L249-L264

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.jacobi_triangular_factor_mul_logDerivative (n : ℕ) :
    (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2) *
      jacobiTriangularLogDerivativeSummand n =
    PowerSeries.derivative ℚ
      (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2) := by sorry
