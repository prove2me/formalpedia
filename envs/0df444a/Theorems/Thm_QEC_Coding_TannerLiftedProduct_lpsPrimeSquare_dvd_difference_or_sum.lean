-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimeSquare_dvd_difference_or_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsPrimeSquare_dvd_difference_or_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:53:24.593782+00:00
-- url     : https://prove2.me/theorems/2640969e-b299-4d31-8097-c7e982140306
-- title:
--   Tanner Lifted Product: lps Prime Square dvd difference or sum
-- statement:
--   The Tanner Lifted Product construction uses the lps Prime Square dvd difference or sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L44-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L44-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsPrimeSquare_dvd_difference_or_sum (q a r : ℤ) (hq : Prime q)
    (hqr : ¬q ∣ 2*r) (h : q^2 ∣ (a-r)*(a+r)) : q^2 ∣ a-r ∨ q^2 ∣ a+r := by sorry
