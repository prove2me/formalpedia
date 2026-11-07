-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobi_even_plus_logDerivative
-- name    : QEC.Coding.TannerLiftedProduct.summable_jacobi_even_plus_logDerivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:23.382467+00:00
-- url     : https://prove2.me/theorems/fa93b9e4-a0c2-46ac-bcc4-d8c1fe140be4
-- title:
--   Tanner Lifted Product: summable jacobi even plus log Derivative
-- statement:
--   The even-plus logarithmic derivative family is summable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L185-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L185-L192

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.summable_jacobi_even_plus_logDerivative :
    Summable (fun n : ℕ => jacobiPlusLogDerivative (2 * (n + 1))) := by sorry
