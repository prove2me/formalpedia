-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiAlternatingThetaProduct_mul_evenMinusProduct
-- name    : QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_mul_evenMinusProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:51:44.588213+00:00
-- url     : https://prove2.me/theorems/579d016b-d55e-4b3c-bfda-5b7316268797
-- title:
--   Tanner Lifted Product: jacobi Alternating Theta Product mul even Minus Product
-- statement:
--   The alternating theta product times its even-minus denominator is
--   Euler's square product. This is the denominator-free form of the usual
--   specialized Jacobi product quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L403-L414
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L403-L414

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

theorem QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_mul_evenMinusProduct :
    jacobiAlternatingThetaProduct * jacobiEvenMinusProduct =
      jacobiEulerSquareProduct := by sorry
