-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_continuous_powerSeries_derivative
-- name    : QEC.Coding.TannerLiftedProduct.continuous_powerSeries_derivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:50:46.613462+00:00
-- url     : https://prove2.me/theorems/14a95538-0494-4ce1-8164-b2a00b9c7c2d
-- title:
--   Tanner Lifted Product: continuous power Series derivative
-- statement:
--   Formal differentiation is continuous for the coefficientwise topology on
--   rational power series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L23-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L23-L34

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

theorem QEC.Coding.TannerLiftedProduct.continuous_powerSeries_derivative :
    Continuous (PowerSeries.derivative ℚ : ℚ⟦X⟧ → ℚ⟦X⟧) := by sorry
