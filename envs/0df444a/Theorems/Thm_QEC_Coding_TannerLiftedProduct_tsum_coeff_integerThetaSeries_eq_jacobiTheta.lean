-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_integerThetaSeries_eq_jacobiTheta
-- name    : QEC.Coding.TannerLiftedProduct.tsum_coeff_integerThetaSeries_eq_jacobiTheta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:27.243354+00:00
-- url     : https://prove2.me/theorems/bbc9118a-6127-4a78-806b-b009ea4a2977
-- title:
--   Tanner Lifted Product: tsum coeff integer Theta Series eq jacobi Theta
-- statement:
--   The analytic Jacobi theta function is the convergent evaluation of the
--   formal integer theta coefficient sequence at `exp(πiτ)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L106-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L106-L159

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.tsum_coeff_integerThetaSeries_eq_jacobiTheta
    (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n integerThetaSeries : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) = jacobiTheta τ := by sorry
