-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleSquaredDistance_le_of_abs_bounds
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerCircleSquaredDistance_le_of_abs_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:46.60575+00:00
-- url     : https://prove2.me/theorems/8bdadd3c-e459-4aea-a983-108d82fde83c
-- title:
--   Tanner Lifted Product: lps Integer Circle Squared Distance le of abs bounds
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Circle Squared Distance le of abs bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L64-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L64-L71

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerCircleSquaredDistance_le_of_abs_bounds
    (a b : ℤ × ℤ) (L : ℤ) (hL : 0 ≤ L)
    (hx : |b.1-a.1| ≤ L) (hy : |b.2-a.2| ≤ L) :
    lpsIntegerCircleSquaredDistance a b ≤ 2*L^2 := by sorry
