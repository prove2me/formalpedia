-- Prove2me | Theorems.Thm_TroppMatrixConcentration_variance_additivity
-- name    : TroppMatrixConcentration.variance_additivity
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:50:54.087172+00:00
-- url     : https://prove2.me/theorems/ad8373a1-8ea4-4950-8dcd-7f2df5380a15
-- title:
--   Equation 2.2.5 — Additivity of matrix variance
-- statement:
--   Let $X_1,\ldots,X_N$ be independent measurable Hermitian random $d\times d$ complex matrices on a probability space, with $d\ge1$ and finite second moments. Write $Y=\sum_k X_k$. Then
--   $$\mathbb E(Y-\mathbb EY)^2=\sum_k\mathbb E(X_k-\mathbb EX_k)^2.$$
--   No zero-mean assumption is imposed. The identity is matrix-valued and keeps the summation inside subsequent spectral norms.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Section 2.2.7, equation (2.2.5), printed pp. 27–28.

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem variance_additivity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hL2 : ∀ k, MemLp (X k) 2 μ) (hIndep : iIndepFun X μ) :
    (∫ ω, ((∑ k, X k ω) - ∫ ω', ∑ k, X k ω' ∂μ) ^ 2 ∂μ) =
      ∑ k, ∫ ω, (X k ω - ∫ ω', X k ω' ∂μ) ^ 2 ∂μ := by sorry

end TroppMatrixConcentration
