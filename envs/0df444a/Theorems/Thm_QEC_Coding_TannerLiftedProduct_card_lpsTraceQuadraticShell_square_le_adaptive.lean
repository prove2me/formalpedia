-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsTraceQuadraticShell_square_le_adaptive
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_square_le_adaptive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:55:59.612637+00:00
-- url     : https://prove2.me/theorems/d0250af3-295d-4e1d-afb2-ffd1e6975420
-- title:
--   Tanner Lifted Product: card lps Trace Quadratic Shell square le adaptive
-- statement:
--   The Tanner Lifted Product construction uses the card lps Trace Quadratic Shell square le adaptive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L191-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L191-L201

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Mathlib.Data.Nat.Find
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAdaptiveThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_square_le_adaptive (q r K : ℕ) (hq : q.Prime) (hK : 0 < K)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (hcap : r^2 ≤ 4*q^2*K^6) :
    (lpsTraceQuadraticShell q (r^2)).card ≤ 1600*(2*r/q^2+1)*K^5 := by sorry
