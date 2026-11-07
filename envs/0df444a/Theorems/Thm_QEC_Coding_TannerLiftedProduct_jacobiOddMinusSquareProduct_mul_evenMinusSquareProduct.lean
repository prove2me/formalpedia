-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiOddMinusSquareProduct_mul_evenMinusSquareProduct
-- name    : QEC.Coding.TannerLiftedProduct.jacobiOddMinusSquareProduct_mul_evenMinusSquareProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:51:38.123438+00:00
-- url     : https://prove2.me/theorems/90e9ba6e-ed9f-4fb4-a32e-11abcbed9016
-- title:
--   Tanner Lifted Product: jacobi Odd Minus Square Product mul even Minus Square Product
-- statement:
--   Splitting all positive exponents into odd and even ones reconstructs
--   Euler's square product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L358-L383
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L358-L383

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

theorem QEC.Coding.TannerLiftedProduct.jacobiOddMinusSquareProduct_mul_evenMinusSquareProduct :
    jacobiOddMinusSquareProduct *
      (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2) =
      jacobiEulerSquareProduct := by sorry
