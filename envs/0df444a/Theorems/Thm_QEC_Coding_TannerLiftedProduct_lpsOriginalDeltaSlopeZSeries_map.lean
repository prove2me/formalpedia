-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaSlopeZSeries_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaSlopeZSeries_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:26.977865+00:00
-- url     : https://prove2.me/theorems/eaca7951-6426-453e-b5ab-d8af19e75dbb
-- title:
--   Tanner Lifted Product: lps Original Delta Slope ZSeries map
-- statement:
--   The actual integer divided slope maps to the SAME existing rational divided slope.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L146-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L146-L151

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaSlopeZSeries_map :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalDeltaSlopeZSeries=lpsOriginalDeltaSlopeQSeries := by sorry
