-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingClosedReducedWordCount_even_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsAlternatingClosedReducedWordCount_even_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:01:40.637944+00:00
-- url     : https://prove2.me/theorems/e9503c1b-5a16-4b68-a89d-0865c09cb671
-- title:
--   Tanner Lifted Product: lps Alternating Closed Reduced Word Count even le
-- statement:
--   The Tanner Lifted Product construction uses the lps Alternating Closed Reduced Word Count even le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L204-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L204-L219

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsAlternatingClosedReducedWordCount_even_le {p : ℕ} (a : LPSResiduePrime p)
    (k K : ℕ) (hK : 0 < K) (hcap : p^(2*k) ≤ 4*a.q^2*K^8) :
    lpsAlternatingClosedReducedWordCount a (2*k) ≤ 96*(2*p^k/a.q^2+1)*K^7 := by sorry
