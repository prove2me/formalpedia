-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4ZSeries_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE4ZSeries_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:49.345672+00:00
-- url     : https://prove2.me/theorems/34a9ea09-b9db-4179-ae3b-748c59955db6
-- title:
--   Tanner Lifted Product: lps Original E4 ZSeries map
-- statement:
--   The actual integer E4 maps to the SAME existing rational E4.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L167-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L167-L170

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE4ZSeries_map :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalE4ZSeries=lpsOriginalEisensteinQSeries 4 := by sorry
