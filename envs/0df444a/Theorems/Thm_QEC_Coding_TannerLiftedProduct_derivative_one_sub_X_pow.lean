-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_one_sub_X_pow
-- name    : QEC.Coding.TannerLiftedProduct.derivative_one_sub_X_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:55:22.310293+00:00
-- url     : https://prove2.me/theorems/1ffdf0e4-6aec-4d38-aaff-eb3bcc4cc877
-- title:
--   Tanner Lifted Product: derivative one sub X pow
-- statement:
--   Formal derivative of an even/odd minus factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L44-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L44-L50

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

theorem QEC.Coding.TannerLiftedProduct.derivative_one_sub_X_pow (d : ℕ) :
    PowerSeries.derivative ℚ
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) =
      -(PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1)) := by sorry
