-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_coeff_integerThetaSeries_mul_pow
-- name    : QEC.Coding.TannerLiftedProduct.summable_norm_coeff_integerThetaSeries_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:45.591506+00:00
-- url     : https://prove2.me/theorems/033673da-cc81-466b-90c9-b1ca854be0ce
-- title:
--   Tanner Lifted Product: summable norm coeff integer Theta Series mul pow
-- statement:
--   The formal integer theta series converges absolutely on the open unit
--   disc.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L40-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L40-L47

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.summable_norm_coeff_integerThetaSeries_mul_pow
    (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n integerThetaSeries : ℕ) : ℂ) * z ^ n‖) := by sorry
