-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiThetaProduct_mul_jacobiTriangularProduct
-- name    : QEC.Coding.TannerLiftedProduct.jacobiThetaProduct_mul_jacobiTriangularProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:52:31.821202+00:00
-- url     : https://prove2.me/theorems/4a2501a2-6884-434c-a303-487ba56521d3
-- title:
--   Tanner Lifted Product: jacobi Theta Product mul jacobi Triangular Product
-- statement:
--   Product algebra for the two Jacobi products: their common even-minus
--   factor squares, while their odd/even plus factors merge into all positive
--   exponents.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L559-L593
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L559-L593

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

theorem QEC.Coding.TannerLiftedProduct.jacobiThetaProduct_mul_jacobiTriangularProduct :
    jacobiThetaProduct * jacobiTriangularProduct =
      jacobiEvenMinusSquareProduct * jacobiAllPlusSquareProduct := by sorry
