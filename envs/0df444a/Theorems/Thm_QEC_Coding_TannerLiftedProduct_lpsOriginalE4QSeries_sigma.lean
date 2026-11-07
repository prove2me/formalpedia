-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4QSeries_sigma
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE4QSeries_sigma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:28.574596+00:00
-- url     : https://prove2.me/theorems/341d82b5-6506-45c7-9ea4-9c0c6c7edbd4
-- title:
--   Tanner Lifted Product: lps Original E4 QSeries sigma
-- statement:
--   Actual Bernoulli-four evaluation identifies the existing rational E4 series with one plus240 sigma3.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L56-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L56-L66

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE4QSeries_sigma : lpsOriginalEisensteinQSeries 4=
    1+PowerSeries.C (240:ℚ)*PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 3) := by sorry
