-- Prove2me | Theorems.Thm_TroppMatrixConcentration_hermitian_bernstein
-- name    : TroppMatrixConcentration.hermitian_bernstein
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:51:51.913272+00:00
-- url     : https://prove2.me/theorems/559bf86a-9927-4dfd-8a82-d48006fe0db9
-- title:
--   Theorem 6.6.1 — Hermitian matrix Bernstein
-- statement:
--   Let $X_k$ be a finite independent family of measurable Hermitian random $d\times d$ matrices with finite second moments, on a probability space, with $d\ge1$. Suppose $\mathbb EX_k=0$ and $\lambda_{\max}(X_k)\le L$ almost surely, for a common $L\ge0$. With $Y=\sum_kX_k$,
--   $$v=\|\mathbb EY^2\|=\left\|\sum_k\mathbb EX_k^2\right\|,$$
--   $$\mathbb E\lambda_{\max}(Y)\le\sqrt{2v\log d}+\frac L3\log d,$$
--   $$\mathbb P\{\lambda_{\max}(Y)\ge t\}\le d\exp\left(-\frac{t^2/2}{v+Lt/3}\right)\quad(t\ge0).$$
--   At a zero denominator, the right-hand side is $d$ for $t=0$ and zero for $t>0$. This is a one-sided result; a bound on the full spectral norm of each $X_k$ is not assumed.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 6.6.1, equations (6.6.1–3), printed pp. 96–99.

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem hermitian_bernstein {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hL2 : ∀ k, MemLp (X k) 2 μ) (hIndep : iIndepFun X μ)
    (hMean : ∀ k, (∫ ω, X k ω ∂μ) = 0)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (X k ω) ≤ L) :
    let Y := fun ω => ∑ k, X k ω
    let v := hermitianSecondMoment μ Y
    v = spectralNorm (∑ k, ∫ ω, X k ω ^ 2 ∂μ) ∧
    (∫ ω, lambdaMax (Y ω) ∂μ) ≤
      Real.sqrt (2 * v * Real.log d) + L * Real.log d / 3 ∧
    ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
      bernsteinTail d v L t := by sorry

end TroppMatrixConcentration
