-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_tsum
-- name    : QEC.Coding.TannerLiftedProduct.derivative_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:55:17.171809+00:00
-- url     : https://prove2.me/theorems/a2b41b1b-b64c-4c3d-a786-f564965a913d
-- title:
--   Tanner Lifted Product: derivative tsum
-- statement:
--   Consequently formal differentiation commutes with any summable family of
--   rational power series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L38-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L38-L41

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

theorem QEC.Coding.TannerLiftedProduct.derivative_tsum {I : Type*} (f : I → ℚ⟦X⟧) (hf : Summable f) :
    PowerSeries.derivative ℚ (∑' i, f i) =
      ∑' i, PowerSeries.derivative ℚ (f i) := by sorry
