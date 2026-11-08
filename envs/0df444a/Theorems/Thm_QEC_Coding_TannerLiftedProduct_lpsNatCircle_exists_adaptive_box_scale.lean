-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_exists_adaptive_box_scale
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatCircle_exists_adaptive_box_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:55:23.91253+00:00
-- url     : https://prove2.me/theorems/0e362b35-bf30-4b0b-a012-c43189435453
-- title:
--   Tanner Lifted Product: lps Nat Circle exists adaptive box scale
-- statement:
--   The Tanner Lifted Product construction uses the lps Nat Circle exists adaptive box scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L35-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L35-L52

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Mathlib.Data.Nat.Find
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAdaptiveThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsNatCircle_exists_adaptive_box_scale (n : ℕ) (hn : 2 < n) :
    ∃ L : ℕ, 0 < L ∧ 2*L^6 < n ∧ n ≤ 128*L^6 := by sorry
