-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiAlternatingThetaProduct_pow_four_mul_theta_triangular
-- name    : QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_pow_four_mul_theta_triangular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:56:41.736304+00:00
-- url     : https://prove2.me/theorems/261e9c0a-c7d0-4d51-bf35-2353547a2402
-- title:
--   Tanner Lifted Product: jacobi Alternating Theta Product pow four mul theta triangular
-- statement:
--   Product-side closure used in Jacobi's four-square proof: the fourth
--   power of the alternating theta product times `βγ` is Euler's sixth-power
--   product. No series identity is assumed here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L608-L622
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L608-L622

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

theorem QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_pow_four_mul_theta_triangular :
    jacobiAlternatingThetaProduct ^ 4 *
        (jacobiThetaProduct * jacobiTriangularProduct) =
      jacobiEulerSixProduct := by sorry
