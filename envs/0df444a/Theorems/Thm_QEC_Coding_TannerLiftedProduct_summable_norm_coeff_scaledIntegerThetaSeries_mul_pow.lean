-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_coeff_scaledIntegerThetaSeries_mul_pow
-- name    : QEC.Coding.TannerLiftedProduct.summable_norm_coeff_scaledIntegerThetaSeries_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:32.1169+00:00
-- url     : https://prove2.me/theorems/42cbdaaf-387b-4007-b19d-2d5b6c41e12b
-- title:
--   Tanner Lifted Product: summable norm coeff scaled Integer Theta Series mul pow
-- statement:
--   The scaled theta series has the same uniform coefficient bound and
--   therefore converges throughout the open unit disc.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L51-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L51-L62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.summable_norm_coeff_scaledIntegerThetaSeries_mul_pow
    (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (scaledIntegerThetaSeries m) : ℕ) : ℂ) * z ^ n‖) := by sorry
