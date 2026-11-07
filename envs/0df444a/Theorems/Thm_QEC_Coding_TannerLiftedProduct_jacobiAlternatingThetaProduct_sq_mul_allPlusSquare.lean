-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiAlternatingThetaProduct_sq_mul_allPlusSquare
-- name    : QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_sq_mul_allPlusSquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:52:19.112193+00:00
-- url     : https://prove2.me/theorems/d1ce73ba-17df-47e6-a8b2-075ece2a02e0
-- title:
--   Tanner Lifted Product: jacobi Alternating Theta Product sq mul all Plus Square
-- statement:
--   Squaring the alternating theta product removes the even-factor
--   denominator: `δ² A₊ = E²` in the standard product notation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L451-L469
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L451-L469

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

theorem QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_sq_mul_allPlusSquare :
    jacobiAlternatingThetaProduct ^ 2 * jacobiAllPlusSquareProduct =
      jacobiEulerSquareProduct := by sorry
