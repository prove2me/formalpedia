-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_tprod_eq_tprod_mul_tsum
-- name    : QEC.Coding.TannerLiftedProduct.derivative_tprod_eq_tprod_mul_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:55:48.021175+00:00
-- url     : https://prove2.me/theorems/7a91f9fe-efac-4ae7-8951-4137b750fe69
-- title:
--   Tanner Lifted Product: derivative tprod eq tprod mul tsum
-- statement:
--   Infinite product rule in logarithmic-derivative form for the
--   coefficientwise topology on rational formal power series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L81-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L81-L107

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

theorem QEC.Coding.TannerLiftedProduct.derivative_tprod_eq_tprod_mul_tsum
    {I : Type*} (f l : I → ℚ⟦X⟧)
    (hf : Multipliable f) (hl : Summable l)
    (hlog : ∀ i, f i * l i = PowerSeries.derivative ℚ (f i)) :
    PowerSeries.derivative ℚ (∏' i, f i) =
      (∏' i, f i) * ∑' i, l i := by sorry
