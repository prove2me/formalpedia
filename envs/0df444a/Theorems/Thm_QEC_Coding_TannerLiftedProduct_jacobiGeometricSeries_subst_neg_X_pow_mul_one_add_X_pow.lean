-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow
-- name    : QEC.Coding.TannerLiftedProduct.jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:10.905296+00:00
-- url     : https://prove2.me/theorems/acc4113e-46c0-4e49-9acc-effce5b877b7
-- title:
--   Tanner Lifted Product: jacobi Geometric Series subst neg X pow mul one add X pow
-- statement:
--   Substitution at `-X^d` produces the inverse of `1 + X^d`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L52-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L52-L62

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow
    {d : ℕ} (hd : d ≠ 0) :
    (jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))) *
      ((1 : ℚ⟦X⟧) + PowerSeries.X ^ d) = 1 := by sorry
