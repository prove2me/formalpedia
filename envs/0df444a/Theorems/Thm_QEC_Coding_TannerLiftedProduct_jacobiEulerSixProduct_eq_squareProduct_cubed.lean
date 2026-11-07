-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiEulerSixProduct_eq_squareProduct_cubed
-- name    : QEC.Coding.TannerLiftedProduct.jacobiEulerSixProduct_eq_squareProduct_cubed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:51:26.5535+00:00
-- url     : https://prove2.me/theorems/e4ffa67b-820a-4822-9e83-68cd2de1b4da
-- title:
--   Tanner Lifted Product: jacobi Euler Six Product eq square Product cubed
-- statement:
--   Euler's sixth-power product is the cube of its square product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L295-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L295-L301

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

theorem QEC.Coding.TannerLiftedProduct.jacobiEulerSixProduct_eq_squareProduct_cubed :
    jacobiEulerSixProduct = jacobiEulerSquareProduct ^ 3 := by sorry
