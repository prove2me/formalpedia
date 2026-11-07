-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tendsto_two_mul_succ_atTop
-- name    : QEC.Coding.TannerLiftedProduct.tendsto_two_mul_succ_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:55:54.851306+00:00
-- url     : https://prove2.me/theorems/a346ef2e-80b2-452c-9aaf-378497a7597a
-- title:
--   Tanner Lifted Product: tendsto two mul succ at Top
-- statement:
--   The exponents `2, 4, 6, ...` tend to infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L110-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L110-L115

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

theorem QEC.Coding.TannerLiftedProduct.tendsto_two_mul_succ_atTop :
    Filter.Tendsto (fun n : ℕ => 2 * (n + 1)) Filter.atTop Filter.atTop := by sorry
