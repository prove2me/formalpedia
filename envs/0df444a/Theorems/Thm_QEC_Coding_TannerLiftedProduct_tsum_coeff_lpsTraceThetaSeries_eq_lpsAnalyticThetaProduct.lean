-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_lpsTraceThetaSeries_eq_lpsAnalyticThetaProduct
-- name    : QEC.Coding.TannerLiftedProduct.tsum_coeff_lpsTraceThetaSeries_eq_lpsAnalyticThetaProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:27.944033+00:00
-- url     : https://prove2.me/theorems/cf3da87d-7feb-489f-b510-fa679493d887
-- title:
--   Tanner Lifted Product: tsum coeff lps Trace Theta Series eq lps Analytic Theta Product
-- statement:
--   The coefficient series evaluates to the named analytic product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L371-L377
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L371-L377

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.tsum_coeff_lpsTraceThetaSeries_eq_lpsAnalyticThetaProduct
    (r : ℕ) (hr : 0 < r) (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) =
      lpsAnalyticThetaProduct r τ := by sorry
