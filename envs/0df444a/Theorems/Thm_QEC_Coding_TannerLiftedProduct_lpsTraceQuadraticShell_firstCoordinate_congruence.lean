-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceQuadraticShell_firstCoordinate_congruence
-- name    : QEC.Coding.TannerLiftedProduct.lpsTraceQuadraticShell_firstCoordinate_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:52:45.580226+00:00
-- url     : https://prove2.me/theorems/15c6ce24-093f-4df5-821f-90e9cf9100ae
-- title:
--   Tanner Lifted Product: lps Trace Quadratic Shell first Coordinate congruence
-- statement:
--   The Tanner Lifted Product construction uses the lps Trace Quadratic Shell first Coordinate congruence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L57-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L57-L67

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsTraceQuadraticShell_firstCoordinate_congruence (q r : ℕ) (hq : q.Prime)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (t : LPSQuaternion)
    (ht : t ∈ lpsTraceQuadraticShell q (r^2)) :
    (q : ℤ)^2 ∣ t.a-(r : ℤ) ∨ (q : ℤ)^2 ∣ t.a+(r : ℤ) := by sorry
