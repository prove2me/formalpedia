-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_mul_mul_pow
-- name    : QEC.Coding.TannerLiftedProduct.tsum_coeff_mul_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:33.074707+00:00
-- url     : https://prove2.me/theorems/a5ef42f2-5a93-49e3-a8e8-b55c318282db
-- title:
--   Tanner Lifted Product: tsum coeff mul mul pow
-- statement:
--   Evaluation of a product of absolutely convergent natural-coefficient
--   formal series agrees with the product of evaluations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L307-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L307-L317

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.tsum_coeff_mul_mul_pow
    (S T : PowerSeries ℕ) (z : ℂ)
    (hS : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n‖))
    (hT : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n T : ℕ) : ℂ) * z ^ n‖)) :
    (∑' n : ℕ, ((PowerSeries.coeff n (S * T) : ℕ) : ℂ) * z ^ n) =
      (∑' n : ℕ, ((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n) *
        (∑' n : ℕ, ((PowerSeries.coeff n T : ℕ) : ℂ) * z ^ n) := by sorry
