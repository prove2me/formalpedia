-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobiTriangularLogDerivativeSummand
-- name    : QEC.Coding.TannerLiftedProduct.summable_jacobiTriangularLogDerivativeSummand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:37.978875+00:00
-- url     : https://prove2.me/theorems/dab6d20c-c3c2-4979-9d58-b7e00811c2f4
-- title:
--   Tanner Lifted Product: summable jacobi Triangular Log Derivative Summand
-- statement:
--   The Tanner Lifted Product construction uses the summable jacobi Triangular Log Derivative Summand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L242-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L242-L245

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.summable_jacobiTriangularLogDerivativeSummand :
    Summable jacobiTriangularLogDerivativeSummand := by sorry
