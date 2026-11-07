-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatSameQuotient_abs_sub_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatSameQuotient_abs_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:42.28507+00:00
-- url     : https://prove2.me/theorems/f03b46fd-cde2-4e31-81b8-23965aeb971d
-- title:
--   Tanner Lifted Product: lps Nat Same Quotient abs sub le
-- statement:
--   The Tanner Lifted Product construction uses the lps Nat Same Quotient abs sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L172-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L172-L179

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsNatSameQuotient_abs_sub_le (a b L : ℕ) (hL : 0 < L)
    (h : a / L = b / L) : |(b : ℤ) - (a : ℤ)| ≤ (L : ℤ) := by sorry
