-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircleBoxRank_eq_imp_quotients_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatCircleBoxRank_eq_imp_quotients_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:49.020805+00:00
-- url     : https://prove2.me/theorems/b5180240-ee5d-4a67-96db-8b1b2983ac2c
-- title:
--   Tanner Lifted Product: lps Nat Circle Box Rank eq imp quotients eq
-- statement:
--   The Tanner Lifted Product construction uses the lps Nat Circle Box Rank eq imp quotients eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L195-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L195-L207

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsNatCircleBoxRank_eq_imp_quotients_eq (a b : ℕ × ℕ) (n M L : ℕ)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n)
    (haB : a.1/L ≤ M ∧ a.2/L ≤ M) (hbB : b.1/L ≤ M ∧ b.2/L ≤ M)
    (h : lpsNatCircleBoxRank M L a = lpsNatCircleBoxRank M L b) :
    a.1/L=b.1/L ∧ a.2/L=b.2/L := by sorry
