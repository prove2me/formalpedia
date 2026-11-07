-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_even_sub
-- name    : QEC.Coding.TannerLiftedProduct.multipliable_jacobi_even_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:50:28.953043+00:00
-- url     : https://prove2.me/theorems/d124d3a4-467b-4e28-8e98-d2da3b2630fd
-- title:
--   Tanner Lifted Product: multipliable jacobi even sub
-- statement:
--   The even factors `1 - X^(2n+2)` form a convergent formal product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L146-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L146-L152

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

theorem QEC.Coding.TannerLiftedProduct.multipliable_jacobi_even_sub :
    Multipliable (fun n : ℕ =>
      (1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) := by sorry
