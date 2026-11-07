-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_finset_prod_eq_prod_mul_sum
-- name    : QEC.Coding.TannerLiftedProduct.derivative_finset_prod_eq_prod_mul_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:51:03.013941+00:00
-- url     : https://prove2.me/theorems/159f0c3a-ceb6-41c1-b62f-6c006919f014
-- title:
--   Tanner Lifted Product: derivative finset prod eq prod mul sum
-- statement:
--   Finite product rule after supplying a logarithmic derivative for every
--   factor. This formulation avoids division and is the finite approximation used
--   for Jacobi's infinite products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L64-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L64-L77

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

theorem QEC.Coding.TannerLiftedProduct.derivative_finset_prod_eq_prod_mul_sum
    {I : Type*} [DecidableEq I] (f l : I → ℚ⟦X⟧)
    (hlog : ∀ i, f i * l i = PowerSeries.derivative ℚ (f i))
    (s : Finset I) :
    PowerSeries.derivative ℚ (∏ i ∈ s, f i) =
      (∏ i ∈ s, f i) * ∑ i ∈ s, l i := by sorry
