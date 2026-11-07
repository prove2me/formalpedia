-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
-- name    : QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:36:09.134825+00:00
-- url     : https://prove2.me/theorems/69b760b3-1dda-435d-bc8d-2b8689456246
-- title:
--   Tanner Lifted Product: coeff lps Trace Theta Series
-- statement:
--   The Tanner Lifted Product construction uses the coeff lps Trace Theta Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceQuadraticForm.lean#L222-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceQuadraticForm.lean#L222-L225

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries (q n : ℕ) :
    PowerSeries.coeff n (lpsTraceThetaSeries q) =
      (lpsTraceQuadraticShell q n).card := by sorry
