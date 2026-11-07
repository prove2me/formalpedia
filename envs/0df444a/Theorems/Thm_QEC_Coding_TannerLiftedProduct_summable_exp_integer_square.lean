-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_exp_integer_square
-- name    : QEC.Coding.TannerLiftedProduct.summable_exp_integer_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:49.795253+00:00
-- url     : https://prove2.me/theorems/46b854d9-7544-456c-9af8-028735e33348
-- title:
--   Tanner Lifted Product: summable exp integer square
-- statement:
--   Mathlib's analytic Jacobi theta summand is absolutely summable in the
--   upper half-plane, in the exact exponent convention of the formal series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L77-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L77-L82

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.summable_exp_integer_square
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun z : ℤ =>
      Complex.exp (Real.pi * Complex.I * (z : ℂ) ^ 2 * τ)) := by sorry
