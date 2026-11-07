-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_coordinates_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatCircle_coordinates_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:50:19.424496+00:00
-- url     : https://prove2.me/theorems/0b5f8b11-380b-4d60-80ce-231329070baa
-- title:
--   Tanner Lifted Product: lps Nat Circle coordinates bound
-- statement:
--   The Tanner Lifted Product construction uses the lps Nat Circle coordinates bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L278-L282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L278-L282

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsNatCircle_coordinates_bound (a : ℕ × ℕ) (n R : ℕ)
    (ha : a.1^2+a.2^2=n) (hn : n ≤ R^2) : a.1 ≤ R ∧ a.2 ≤ R := by sorry
