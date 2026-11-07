-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_real_shift
-- name    : QEC.Coding.TannerLiftedProduct.lpsQParam_real_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:02.238547+00:00
-- url     : https://prove2.me/theorems/d1c82023-0e73-4ba2-8f15-2f760f809deb
-- title:
--   Tanner Lifted Product: lps QParam real shift
-- statement:
--   Rational translation contributes the actual standard additive-character phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L51-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L51-L59

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQParam_real_shift (N : ℕ) [NeZero N] (a : ℤ) (z : ℍ) :
    Function.Periodic.qParam 1 (((a:ℝ)/(N:ℝ)) +ᵥ z : ℍ) =
      ZMod.stdAddChar (a:ZMod N)*Function.Periodic.qParam 1 (z:ℂ) := by sorry
