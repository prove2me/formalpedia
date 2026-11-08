-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsTraceCongruenceShell_square_le
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsTraceCongruenceShell_square_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:53:49.657078+00:00
-- url     : https://prove2.me/theorems/4645d70a-8f4e-4264-b4c9-c1910a4d6fff
-- title:
--   Tanner Lifted Product: card lps Trace Congruence Shell square le
-- statement:
--   The Tanner Lifted Product construction uses the card lps Trace Congruence Shell square le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L182-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L182-L191

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.card_lpsTraceCongruenceShell_square_le (q r K : ℕ) (hq : q.Prime) (hK : 0 < K)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (hcap : r^2 ≤ 4*q^2*K^8) :
    (lpsTraceCongruenceShell q (r^2)).card ≤ 192*(2*r/q^2+1)*K^7 := by sorry
