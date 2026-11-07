-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_theta_factor
-- name    : QEC.Coding.TannerLiftedProduct.multipliable_jacobi_theta_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:51:00.218755+00:00
-- url     : https://prove2.me/theorems/c8cea382-66f4-4f64-b76b-f3381dd9c39c
-- title:
--   Tanner Lifted Product: multipliable jacobi theta factor
-- statement:
--   The product combining one even-minus factor and two odd-plus factors
--   exists coefficientwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L179-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L179-L183

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

theorem QEC.Coding.TannerLiftedProduct.multipliable_jacobi_theta_factor :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) := by sorry
