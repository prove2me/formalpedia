-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceQuadraticForm_decompose
-- name    : QEC.Coding.TannerLiftedProduct.lpsTraceQuadraticForm_decompose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:51:12.70282+00:00
-- url     : https://prove2.me/theorems/167db27b-2b19-4c06-ac4e-32ed62e073b7
-- title:
--   Tanner Lifted Product: lps Trace Quadratic Form decompose
-- statement:
--   The Tanner Lifted Product construction uses the lps Trace Quadratic Form decompose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L38-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L38-L42

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsTraceQuadraticForm_decompose (q : ℕ) (t : LPSQuaternion) :
    lpsTraceQuadraticForm q t = t.a^2+4*(q : ℤ)^2*(t.b^2+t.c^2+t.d^2) := by sorry
