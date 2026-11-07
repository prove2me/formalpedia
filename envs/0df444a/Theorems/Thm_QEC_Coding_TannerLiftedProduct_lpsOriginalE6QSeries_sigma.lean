-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE6QSeries_sigma
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE6QSeries_sigma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:23.960067+00:00
-- url     : https://prove2.me/theorems/e1002d9a-9e27-43cf-b854-c7f8171eafdc
-- title:
--   Tanner Lifted Product: lps Original E6 QSeries sigma
-- statement:
--   Actual Bernoulli-six evaluation identifies the existing rational E6 series with one minus504 sigma5.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L69-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L69-L83

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE6QSeries_sigma : lpsOriginalEisensteinQSeries 6=
    1-PowerSeries.C (504:ℚ)*PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 5) := by sorry
