-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaSlopeZSeries_constant
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaSlopeZSeries_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:32.017378+00:00
-- url     : https://prove2.me/theorems/b4935ba2-2a15-4cc5-b39e-531696438ca8
-- title:
--   Tanner Lifted Product: lps Original Delta Slope ZSeries constant
-- statement:
--   The actual integer divided slope has constant one through the faithful coefficient map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L154-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L154-L160

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaSlopeZSeries_constant :
    PowerSeries.constantCoeff lpsOriginalDeltaSlopeZSeries=1 := by sorry
