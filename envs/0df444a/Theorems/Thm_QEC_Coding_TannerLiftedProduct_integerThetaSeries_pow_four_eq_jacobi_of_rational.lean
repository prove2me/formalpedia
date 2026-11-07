-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerThetaSeries_pow_four_eq_jacobi_of_rational
-- name    : QEC.Coding.TannerLiftedProduct.integerThetaSeries_pow_four_eq_jacobi_of_rational
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:54:36.437148+00:00
-- url     : https://prove2.me/theorems/7116af51-8608-410d-8fd7-555fdba64b92
-- title:
--   Tanner Lifted Product: integer Theta Series pow four eq jacobi of rational
-- statement:
--   Equality after coefficient extension to `ℚ` reflects the original
--   natural-coefficient Jacobi theta identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L422-L428
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L422-L428

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.integerThetaSeries_pow_four_eq_jacobi_of_rational
    (h : rationalIntegerThetaSeries ^ 4 = jacobiLambertSeries) :
    integerThetaSeries ^ 4 = jacobiFourSquareSeries := by sorry
