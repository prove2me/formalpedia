-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobi_even_minus_logDerivative
-- name    : QEC.Coding.TannerLiftedProduct.summable_jacobi_even_minus_logDerivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:40.101129+00:00
-- url     : https://prove2.me/theorems/ee253960-9cfd-4646-b559-d7236e4a94aa
-- title:
--   Tanner Lifted Product: summable jacobi even minus log Derivative
-- statement:
--   The even-minus logarithmic derivative family is summable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L165-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L165-L172

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.summable_jacobi_even_minus_logDerivative :
    Summable (fun n : ℕ => jacobiMinusLogDerivative (2 * (n + 1))) := by sorry
