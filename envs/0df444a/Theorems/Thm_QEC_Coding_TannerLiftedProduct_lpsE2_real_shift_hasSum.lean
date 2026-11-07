-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_real_shift_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2_real_shift_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:07.87981+00:00
-- url     : https://prove2.me/theorems/45d9f518-db28-4ef4-a3f7-17a8eb5eaa99
-- title:
--   Tanner Lifted Product: lps E2 real shift has Sum
-- statement:
--   The actual shifted E2 function has its convergent phased divisor series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L62-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L62-L80

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2_real_shift_hasSum (N : ℕ) [NeZero N] (a : ℤ) (z : ℍ) :
    HasSum (fun n : ℕ =>
      (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n : ℂ) *
        ZMod.stdAddChar (((a*(n:ℤ)):ℤ):ZMod N) *
        Function.Periodic.qParam 1 (z:ℂ)^n)
      (EisensteinSeries.E2 (((a:ℝ)/(N:ℝ)) +ᵥ z)) := by sorry
