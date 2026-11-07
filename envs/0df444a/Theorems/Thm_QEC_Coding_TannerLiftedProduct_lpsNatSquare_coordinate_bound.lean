-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatSquare_coordinate_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatSquare_coordinate_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:50.433068+00:00
-- url     : https://prove2.me/theorems/0c45e654-2236-4a0d-9975-929c4eeac92b
-- title:
--   Tanner Lifted Product: lps Nat Square coordinate bound
-- statement:
--   The Tanner Lifted Product construction uses the lps Nat Square coordinate bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L275-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L275-L276

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsNatSquare_coordinate_bound (x n R : ℕ) (hx : x^2 ≤ n) (hn : n ≤ R^2) : x ≤ R := by sorry
