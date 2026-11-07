-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_scaledIntegerThetaSeries_eq_jacobiTheta
-- name    : QEC.Coding.TannerLiftedProduct.tsum_coeff_scaledIntegerThetaSeries_eq_jacobiTheta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:36.184216+00:00
-- url     : https://prove2.me/theorems/a656ccbe-3933-4857-87ae-59b5c5e86a31
-- title:
--   Tanner Lifted Product: tsum coeff scaled Integer Theta Series eq jacobi Theta
-- statement:
--   The scaled formal theta coefficients evaluate to the Jacobi theta
--   function at the correspondingly scaled upper-half-plane argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L184-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L184-L274

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.tsum_coeff_scaledIntegerThetaSeries_eq_jacobiTheta
    (m : ℕ) (hm : 0 < m) (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (scaledIntegerThetaSeries m) : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) =
      jacobiTheta ((m ^ 2 : ℕ) * τ) := by sorry
