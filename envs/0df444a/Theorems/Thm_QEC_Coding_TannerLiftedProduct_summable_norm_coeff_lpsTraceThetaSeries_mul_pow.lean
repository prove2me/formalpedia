-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_coeff_lpsTraceThetaSeries_mul_pow
-- name    : QEC.Coding.TannerLiftedProduct.summable_norm_coeff_lpsTraceThetaSeries_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:46.131199+00:00
-- url     : https://prove2.me/theorems/9577fd06-a23d-4c3b-a5e0-ac05168fafd2
-- title:
--   Tanner Lifted Product: summable norm coeff lps Trace Theta Series mul pow
-- statement:
--   The LPS trace-theta coefficient series converges absolutely at every
--   point of the open unit disc.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L462-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L462-L480

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.summable_norm_coeff_lpsTraceThetaSeries_mul_pow
    (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) * z ^ n‖) := by sorry
