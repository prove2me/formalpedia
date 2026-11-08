-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsTraceQuadraticShell_square_le
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_square_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:54:19.281192+00:00
-- url     : https://prove2.me/theorems/190daf70-f737-40fb-8d91-40e24268a48d
-- title:
--   Tanner Lifted Product: card lps Trace Quadratic Shell square le
-- statement:
--   The Tanner Lifted Product construction uses the card lps Trace Quadratic Shell square le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L170-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L170-L180

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_square_le (q r K : ℕ) (hq : q.Prime) (hK : 0 < K)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (hcap : r^2 ≤ 4*q^2*K^8) :
    (lpsTraceQuadraticShell q (r^2)).card ≤ 192*(2*r/q^2+1)*K^7 := by sorry
