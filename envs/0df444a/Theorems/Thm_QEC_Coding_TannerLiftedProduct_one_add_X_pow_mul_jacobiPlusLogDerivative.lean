-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_one_add_X_pow_mul_jacobiPlusLogDerivative
-- name    : QEC.Coding.TannerLiftedProduct.one_add_X_pow_mul_jacobiPlusLogDerivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:36.269981+00:00
-- url     : https://prove2.me/theorems/00cd3084-b5a6-472a-a67f-026238bbfc9a
-- title:
--   Tanner Lifted Product: one add X pow mul jacobi Plus Log Derivative
-- statement:
--   Multiplying the plus-factor logarithmic derivative by its factor
--   recovers the ordinary derivative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L96-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L96-L112

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.one_add_X_pow_mul_jacobiPlusLogDerivative
    {d : ℕ} (hd : d ≠ 0) :
    ((1 : ℚ⟦X⟧) + PowerSeries.X ^ d) * jacobiPlusLogDerivative d =
      PowerSeries.derivative ℚ
        ((1 : ℚ⟦X⟧) + PowerSeries.X ^ d) := by sorry
