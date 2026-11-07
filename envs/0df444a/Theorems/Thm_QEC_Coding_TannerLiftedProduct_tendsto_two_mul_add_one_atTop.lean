-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tendsto_two_mul_add_one_atTop
-- name    : QEC.Coding.TannerLiftedProduct.tendsto_two_mul_add_one_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:55:51.005173+00:00
-- url     : https://prove2.me/theorems/7920fcbc-3e92-496e-8c2c-0d6514945cf1
-- title:
--   Tanner Lifted Product: tendsto two mul add one at Top
-- statement:
--   The exponents `1, 3, 5, ...` tend to infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L118-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L118-L123

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.tendsto_two_mul_add_one_atTop :
    Filter.Tendsto (fun n : ℕ => 2 * n + 1) Filter.atTop Filter.atTop := by sorry
