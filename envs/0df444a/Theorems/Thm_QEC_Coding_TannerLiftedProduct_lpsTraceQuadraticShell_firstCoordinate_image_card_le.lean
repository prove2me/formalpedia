-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceQuadraticShell_firstCoordinate_image_card_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsTraceQuadraticShell_firstCoordinate_image_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:50:35.927865+00:00
-- url     : https://prove2.me/theorems/c593e53a-f572-46a7-8d12-5409ee62000f
-- title:
--   Tanner Lifted Product: lps Trace Quadratic Shell first Coordinate image card le
-- statement:
--   The Tanner Lifted Product construction uses the lps Trace Quadratic Shell first Coordinate image card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L135-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L135-L168

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsTraceQuadraticShell_firstCoordinate_image_card_le (q r : ℕ) (hq : q.Prime)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) :
    ((lpsTraceQuadraticShell q (r^2)).image LPSQuaternion.a).card ≤ 2*(2*r/q^2+1) := by sorry
