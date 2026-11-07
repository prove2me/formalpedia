-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries_eq_congruenceShell
-- name    : QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_eq_congruenceShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:36:18.862561+00:00
-- url     : https://prove2.me/theorems/4c04a931-c0f8-42f2-8b3a-dff382935649
-- title:
--   Tanner Lifted Product: coeff lps Trace Theta Series eq congruence Shell
-- statement:
--   Positive coefficients of the theta series are exactly the quaternion
--   congruence counts in the finite LPS trace formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceQuadraticForm.lean#L229-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceQuadraticForm.lean#L229-L234

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_eq_congruenceShell
    {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    PowerSeries.coeff n (lpsTraceThetaSeries q) =
      (lpsTraceCongruenceShell q n).card := by sorry
