-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_coeff_mul_mul_pow
-- name    : QEC.Coding.TannerLiftedProduct.summable_norm_coeff_mul_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:27.257867+00:00
-- url     : https://prove2.me/theorems/e01294e9-2551-4d6c-9576-e8036b579ed8
-- title:
--   Tanner Lifted Product: summable norm coeff mul mul pow
-- statement:
--   Absolute convergence is stable under multiplying two natural-coefficient
--   formal power series at a given complex argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L294-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L294-L303

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.summable_norm_coeff_mul_mul_pow
    (S T : PowerSeries ℕ) (z : ℂ)
    (hS : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n‖))
    (hT : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n T : ℕ) : ℂ) * z ^ n‖)) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (S * T) : ℕ) : ℂ) * z ^ n‖) := by sorry
