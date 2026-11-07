-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerPositiveCircle_strict_antitone
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerPositiveCircle_strict_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:45.447982+00:00
-- url     : https://prove2.me/theorems/8e0260f7-556c-4748-a317-2b46ff132c57
-- title:
--   Tanner Lifted Product: lps Integer Positive Circle strict antitone
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Positive Circle strict antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L156-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L156-L161

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerPositiveCircle_strict_antitone
    (x y x' y' n : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x') (hy' : 0 ≤ y')
    (h : x^2+y^2=n) (h' : x'^2+y'^2=n) (hxx : x<x') : y'<y := by sorry
