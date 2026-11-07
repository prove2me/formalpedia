-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJZSeries_mapQ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJZSeries_mapQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:53.761756+00:00
-- url     : https://prove2.me/theorems/564ca62f-d727-4f90-8dfe-f1d705912716
-- title:
--   Tanner Lifted Product: lps Original JZSeries map Q
-- statement:
--   The actual integer K series maps to the SAME existing rational K by genuine unit cancellation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L177-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L177-L193

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJZSeries_mapQ :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalJZSeries=lpsOriginalJQSeries := by sorry
