-- Prove2me | Theorems.Thm_TroppMatrixConcentration_dilation_variance
-- name    : TroppMatrixConcentration.dilation_variance
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:51:18.726529+00:00
-- url     : https://prove2.me/theorems/144b523a-3c74-4b0d-928d-94e111427f1f
-- title:
--   Equation 2.2.10 — Variance statistic under dilation
-- statement:
--   Let $Z$ be a measurable complex $m\times n$ random matrix with finite second moment on a probability space, where $m,n\ge1$. Put $C=Z-\mathbb EZ$. Then
--   $$\left\|\mathbb E H(C)^2\right\|=\max\{\|\mathbb E CC^*\|,\|\mathbb E C^*C\|\}.$$
--   This is the equality of the matrix variance statistic of a Hermitian dilation and that of the original rectangular random matrix. Centering is explicit and no zero-mean assumption is needed.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Section 2.2.8, equations (2.2.7–10), printed pp. 28–29.

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem dilation_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n : ℕ} [NeZero m] [NeZero n]
    (Z : Ω → Matrix (Fin m) (Fin n) ℂ) (hMeas : Measurable Z)
    (hL2 : MemLp Z 2 μ) :
    hermitianSecondMoment μ (fun ω => dilation (Z ω - ∫ ω', Z ω' ∂μ)) =
      rectSecondMoment μ (fun ω => Z ω - ∫ ω', Z ω' ∂μ) := by sorry

end TroppMatrixConcentration
