-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleThreeDistinct_det_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerCircleThreeDistinct_det_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:46.548894+00:00
-- url     : https://prove2.me/theorems/29196338-1c4b-4ba5-875c-e6a956cfb638
-- title:
--   Tanner Lifted Product: lps Integer Circle Three Distinct det ne zero
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Circle Three Distinct det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L99-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L99-L114

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerCircleThreeDistinct_det_ne_zero
    (a b c : ℤ × ℤ) (n : ℤ)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hc : c.1^2+c.2^2=n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    lpsIntegerCircleChordDet a b c ≠ 0 := by sorry
