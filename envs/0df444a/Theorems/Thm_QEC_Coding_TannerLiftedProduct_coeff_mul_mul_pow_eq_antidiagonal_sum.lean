-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_mul_mul_pow_eq_antidiagonal_sum
-- name    : QEC.Coding.TannerLiftedProduct.coeff_mul_mul_pow_eq_antidiagonal_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:49.774565+00:00
-- url     : https://prove2.me/theorems/f6918ded-53e1-4297-97af-673b3b6c12f0
-- title:
--   Tanner Lifted Product: coeff mul mul pow eq antidiagonal sum
-- statement:
--   Coefficientwise Cauchy product after complex evaluation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L277-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L277-L290

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_mul_mul_pow_eq_antidiagonal_sum
    (S T : PowerSeries ℕ) (z : ℂ) (n : ℕ) :
    ((PowerSeries.coeff n (S * T) : ℕ) : ℂ) * z ^ n =
      ∑ kl ∈ Finset.antidiagonal n,
        (((PowerSeries.coeff kl.1 S : ℕ) : ℂ) * z ^ kl.1) *
          (((PowerSeries.coeff kl.2 T : ℕ) : ℂ) * z ^ kl.2) := by sorry
