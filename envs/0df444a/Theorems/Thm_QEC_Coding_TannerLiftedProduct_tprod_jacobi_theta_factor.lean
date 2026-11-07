-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tprod_jacobi_theta_factor
-- name    : QEC.Coding.TannerLiftedProduct.tprod_jacobi_theta_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:55:53.911622+00:00
-- url     : https://prove2.me/theorems/c6373825-f647-4afa-9eef-874c2eef52d1
-- title:
--   Tanner Lifted Product: tprod jacobi theta factor
-- statement:
--   Split the combined Jacobi theta product into its even and odd products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L186-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L186-L200

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

theorem QEC.Coding.TannerLiftedProduct.tprod_jacobi_theta_factor :
    (∏' n : ℕ,
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) =
      (∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))) *
        (∏' n : ℕ, ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1))) ^ 2 := by sorry
