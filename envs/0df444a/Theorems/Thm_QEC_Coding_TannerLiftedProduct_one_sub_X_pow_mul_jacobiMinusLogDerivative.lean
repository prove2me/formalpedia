-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_one_sub_X_pow_mul_jacobiMinusLogDerivative
-- name    : QEC.Coding.TannerLiftedProduct.one_sub_X_pow_mul_jacobiMinusLogDerivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:29.971349+00:00
-- url     : https://prove2.me/theorems/514df28d-88b7-404b-8539-984e9195ec3e
-- title:
--   Tanner Lifted Product: one sub X pow mul jacobi Minus Log Derivative
-- statement:
--   Multiplying the minus-factor logarithmic derivative by its factor
--   recovers the ordinary derivative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L71-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L71-L87

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.one_sub_X_pow_mul_jacobiMinusLogDerivative
    {d : ℕ} (hd : d ≠ 0) :
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) * jacobiMinusLogDerivative d =
      PowerSeries.derivative ℚ
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) := by sorry
