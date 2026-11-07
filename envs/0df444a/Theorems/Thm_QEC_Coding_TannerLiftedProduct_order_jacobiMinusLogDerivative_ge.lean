-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_order_jacobiMinusLogDerivative_ge
-- name    : QEC.Coding.TannerLiftedProduct.order_jacobiMinusLogDerivative_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:18.718113+00:00
-- url     : https://prove2.me/theorems/61a1d3c3-376b-46f2-8a71-b57807cdb85b
-- title:
--   Tanner Lifted Product: order jacobi Minus Log Derivative ge
-- statement:
--   The minus logarithmic-derivative term has no coefficients below degree
--   `d - 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L116-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L116-L137

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.order_jacobiMinusLogDerivative_ge (d : ℕ) :
    (d - 1 : ℕ∞) ≤ (jacobiMinusLogDerivative d).order := by sorry
