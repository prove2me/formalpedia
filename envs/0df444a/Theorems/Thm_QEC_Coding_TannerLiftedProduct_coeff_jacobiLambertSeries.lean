-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiLambertSeries
-- name    : QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:01.483063+00:00
-- url     : https://prove2.me/theorems/9c0a3204-333f-4df9-8932-0184bb7a53e1
-- title:
--   Tanner Lifted Product: coeff jacobi Lambert Series
-- statement:
--   Coefficients of the Lambert series are exactly eight times the sum of
--   positive divisors not divisible by four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L361-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L361-L405

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertSeries (n : ℕ) :
    PowerSeries.coeff n jacobiLambertSeries =
      if n = 0 then 1
      else 8 * ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d := by sorry
