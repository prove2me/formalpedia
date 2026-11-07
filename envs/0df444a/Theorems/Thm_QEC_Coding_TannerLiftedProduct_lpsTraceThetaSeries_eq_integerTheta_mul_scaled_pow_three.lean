-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three
-- name    : QEC.Coding.TannerLiftedProduct.lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:38:27.519167+00:00
-- url     : https://prove2.me/theorems/c0bbbb8a-72d2-4312-8032-cc4f4bf9a1d8
-- title:
--   Tanner Lifted Product: lps Trace Theta Series eq integer Theta mul scaled pow three
-- statement:
--   Concretely, the trace theta series has one ordinary unary theta factor
--   and three factors scaled by `2q`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L266-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L266-L273

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three
    {q : ℕ} (hq : 0 < q) :
    lpsTraceThetaSeries q =
      integerThetaSeries * scaledIntegerThetaSeries (2 * q) ^ 3 := by sorry
