-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiEvenMinusSquareProduct_eq_eulerSquare_mul_allPlusSquare
-- name    : QEC.Coding.TannerLiftedProduct.jacobiEvenMinusSquareProduct_eq_eulerSquare_mul_allPlusSquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:51:03.922928+00:00
-- url     : https://prove2.me/theorems/ccb6d50f-e978-4cdf-9528-571dfb664bdd
-- title:
--   Tanner Lifted Product: jacobi Even Minus Square Product eq euler Square mul all Plus Square
-- statement:
--   Factoring `1 - X^(2k)` as `(1 - X^k)(1 + X^k)` identifies
--   the even-minus square product with the product of the two full square
--   products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L437-L447
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L437-L447

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

theorem QEC.Coding.TannerLiftedProduct.jacobiEvenMinusSquareProduct_eq_eulerSquare_mul_allPlusSquare :
    jacobiEvenMinusSquareProduct =
      jacobiEulerSquareProduct * jacobiAllPlusSquareProduct := by sorry
