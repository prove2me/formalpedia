-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaZSeries_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaZSeries_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:26.770118+00:00
-- url     : https://prove2.me/theorems/53de617f-6c77-493c-920a-1ac45c892660
-- title:
--   Tanner Lifted Product: lps Original Delta ZSeries map
-- statement:
--   Actual integer Delta maps to the SAME existing rational Delta by genuine ring cancellation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L111-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L111-L139

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaZSeries_map :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalDeltaZSeries=lpsOriginalDeltaQSeries := by sorry
