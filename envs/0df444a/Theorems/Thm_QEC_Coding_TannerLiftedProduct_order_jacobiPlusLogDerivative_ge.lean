-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_order_jacobiPlusLogDerivative_ge
-- name    : QEC.Coding.TannerLiftedProduct.order_jacobiPlusLogDerivative_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:41.06264+00:00
-- url     : https://prove2.me/theorems/b1097dfc-a392-4b48-b045-b0ce4603aab4
-- title:
--   Tanner Lifted Product: order jacobi Plus Log Derivative ge
-- statement:
--   The plus logarithmic-derivative term has no coefficients below degree
--   `d - 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L141-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L141-L162

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.order_jacobiPlusLogDerivative_ge (d : ℕ) :
    (d - 1 : ℕ∞) ≤ (jacobiPlusLogDerivative d).order := by sorry
