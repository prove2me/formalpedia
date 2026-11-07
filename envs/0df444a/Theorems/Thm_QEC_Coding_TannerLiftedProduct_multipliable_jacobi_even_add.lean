-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_even_add
-- name    : QEC.Coding.TannerLiftedProduct.multipliable_jacobi_even_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:50:44.766747+00:00
-- url     : https://prove2.me/theorems/c8c25c65-7774-4d4e-bb6f-61531de09acd
-- title:
--   Tanner Lifted Product: multipliable jacobi even add
-- statement:
--   The even factors `1 + X^(2n+2)` form a convergent formal product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L155-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L155-L159

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

theorem QEC.Coding.TannerLiftedProduct.multipliable_jacobi_even_add :
    Multipliable (fun n : ℕ =>
      (1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1))) := by sorry
