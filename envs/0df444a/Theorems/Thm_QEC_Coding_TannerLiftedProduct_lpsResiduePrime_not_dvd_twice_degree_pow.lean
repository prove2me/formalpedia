-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrime_not_dvd_twice_degree_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsResiduePrime_not_dvd_twice_degree_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:50:30.006211+00:00
-- url     : https://prove2.me/theorems/725775dd-2c40-4d18-88ec-6948d192db20
-- title:
--   Tanner Lifted Product: lps Residue Prime not dvd twice degree pow
-- statement:
--   The Tanner Lifted Product construction uses the lps Residue Prime not dvd twice degree pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L193-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L193-L202

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsResiduePrime_not_dvd_twice_degree_pow {p : ℕ} (a : LPSResiduePrime p) (k : ℕ) :
    ¬(a.q : ℤ) ∣ 2*((p : ℤ)^k) := by sorry
