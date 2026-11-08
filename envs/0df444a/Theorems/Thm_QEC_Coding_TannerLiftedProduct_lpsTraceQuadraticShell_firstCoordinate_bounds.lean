-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceQuadraticShell_firstCoordinate_bounds
-- name    : QEC.Coding.TannerLiftedProduct.lpsTraceQuadraticShell_firstCoordinate_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:53:02.644176+00:00
-- url     : https://prove2.me/theorems/eb63c737-dd70-482b-bb2e-5a4e0adb9193
-- title:
--   Tanner Lifted Product: lps Trace Quadratic Shell first Coordinate bounds
-- statement:
--   The Tanner Lifted Product construction uses the lps Trace Quadratic Shell first Coordinate bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L69-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L69-L79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsTraceQuadraticShell_firstCoordinate_bounds (q r : ℕ) (hq : 0 < q)
    (t : LPSQuaternion) (ht : t ∈ lpsTraceQuadraticShell q (r^2)) :
    -(r : ℤ) ≤ t.a ∧ t.a ≤ (r : ℤ) := by sorry
