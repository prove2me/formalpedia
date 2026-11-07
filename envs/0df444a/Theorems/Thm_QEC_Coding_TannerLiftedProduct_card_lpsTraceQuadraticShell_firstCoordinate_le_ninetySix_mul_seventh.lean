-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsTraceQuadraticShell_firstCoordinate_le_ninetySix_mul_seventh
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_firstCoordinate_le_ninetySix_mul_seventh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:55:15.967985+00:00
-- url     : https://prove2.me/theorems/13b4d8e7-5cd7-4a4a-b254-08bef1a1617a
-- title:
--   Tanner Lifted Product: card lps Trace Quadratic Shell first Coordinate le ninety Six mul seventh
-- statement:
--   The Tanner Lifted Product construction uses the card lps Trace Quadratic Shell first Coordinate le ninety Six mul seventh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L403-L456
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L403-L456

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_firstCoordinate_le_ninetySix_mul_seventh
    (q n K : ℕ) (hq : 0 < q) (hK : 0 < K) (hn : n ≤ 4*q^2*K^8) (x : ℤ) :
    ((lpsTraceQuadraticShell q n).filter fun t => t.a=x).card ≤ 96*K^7 := by sorry
