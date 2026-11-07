-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_lpsTraceThetaSeries_eq_lpsStandardTheta
-- name    : QEC.Coding.TannerLiftedProduct.tsum_coeff_lpsTraceThetaSeries_eq_lpsStandardTheta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:42.65999+00:00
-- url     : https://prove2.me/theorems/cbaf944f-c79f-4078-8481-1eabf18805d0
-- title:
--   Tanner Lifted Product: tsum coeff lps Trace Theta Series eq lps Standard Theta
-- statement:
--   The formal trace-theta coefficient at `n` is exactly the coefficient
--   of `exp (2πiz)^n` in the standard analytic coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L424-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L424-L439

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.tsum_coeff_lpsTraceThetaSeries_eq_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : 0 < z.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * z) ^ n) =
      lpsStandardTheta r z := by sorry
