-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiThetaProduct_mul_jacobiTriangularProduct_eq_eulerSquare
-- name    : QEC.Coding.TannerLiftedProduct.jacobiThetaProduct_mul_jacobiTriangularProduct_eq_eulerSquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:52:32.295806+00:00
-- url     : https://prove2.me/theorems/29bd9749-f76d-49c9-8cc3-058922973fbc
-- title:
--   Tanner Lifted Product: jacobi Theta Product mul jacobi Triangular Product eq euler Square
-- statement:
--   Sambale's product simplification for `βγ`: after the even/odd split,
--   the two Jacobi products become Euler's square product times the square of
--   the full plus-square product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L598-L603
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L598-L603

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

theorem QEC.Coding.TannerLiftedProduct.jacobiThetaProduct_mul_jacobiTriangularProduct_eq_eulerSquare :
    jacobiThetaProduct * jacobiTriangularProduct =
      jacobiEulerSquareProduct * jacobiAllPlusSquareProduct ^ 2 := by sorry
