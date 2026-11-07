-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsTraceQuadraticShell_eq_congruenceShell
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_eq_congruenceShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:36:10.804301+00:00
-- url     : https://prove2.me/theorems/49f24675-568f-45b1-806c-691d6eebc228
-- title:
--   Tanner Lifted Product: card lps Trace Quadratic Shell eq congruence Shell
-- statement:
--   The representation number of `Q_q` is exactly the finite quaternion
--   congruence count appearing in the LPS trace calculation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceQuadraticForm.lean#L209-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceQuadraticForm.lean#L209-L215

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_eq_congruenceShell
    {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    (lpsTraceQuadraticShell q n).card =
      (lpsTraceCongruenceShell q n).card := by sorry
