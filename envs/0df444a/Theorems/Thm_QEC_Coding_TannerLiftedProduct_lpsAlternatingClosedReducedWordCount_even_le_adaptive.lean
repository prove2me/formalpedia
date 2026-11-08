-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingClosedReducedWordCount_even_le_adaptive
-- name    : QEC.Coding.TannerLiftedProduct.lpsAlternatingClosedReducedWordCount_even_le_adaptive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:01:13.197132+00:00
-- url     : https://prove2.me/theorems/9d785490-f243-48bb-823c-e9fa54e6b038
-- title:
--   Tanner Lifted Product: lps Alternating Closed Reduced Word Count even le adaptive
-- statement:
--   The Tanner Lifted Product construction uses the lps Alternating Closed Reduced Word Count even le adaptive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L214-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L214-L229

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Mathlib.Data.Nat.Find
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAdaptiveThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsAlternatingClosedReducedWordCount_even_le_adaptive {p : ℕ} (a : LPSResiduePrime p)
    (k K : ℕ) (hK : 0 < K) (hcap : p^(2*k) ≤ 4*a.q^2*K^6) :
    lpsAlternatingClosedReducedWordCount a (2*k) ≤ 800*(2*p^k/a.q^2+1)*K^5 := by sorry
