-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch5_matrix_chernoff
-- name    : TroppMatrixConcentration.ch5_matrix_chernoff
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:48:39.98407+00:00
-- url     : https://prove2.me/theorems/11dd0777-9371-460c-9fb1-e2b2a36f98fe
-- title:
--   Theorem 5.1.1 — Matrix Chernoff, both spectral sides
-- statement:
--   Let $X_k$ be a finite independent family of measurable random complex $d\times d$ matrices on a probability space, with $d\ge1$. Assume each $X_k$ is Hermitian almost surely and satisfies $0\le\lambda_{\min}(X_k)$ and $\lambda_{\max}(X_k)\le L$ almost surely, for a common $L\ge0$. Define $Y=\sum_k X_k$, $a=\lambda_{\min}(\mathbb EY)$, and $b=\lambda_{\max}(\mathbb EY)$. Then
--   $$a=\lambda_{\min}\left(\sum_k\mathbb EX_k\right),\qquad b=\lambda_{\max}\left(\sum_k\mathbb EX_k\right).$$
--   For every $\theta>0$, both expectation inequalities hold:
--   $$\mathbb E\lambda_{\min}(Y)\ge\frac{1-e^{-\theta}}{\theta}a-\frac{L\log d}{\theta},\qquad\mathbb E\lambda_{\max}(Y)\le\frac{e^\theta-1}{\theta}b+\frac{L\log d}{\theta}.$$
--   For $0\le\varepsilon<1$,
--   $$\mathbb P\{\lambda_{\min}(Y)\le(1-\varepsilon)a\}\le d\left[\frac{e^{-\varepsilon}}{(1-\varepsilon)^{1-\varepsilon}}\right]^{a/L}.$$
--   For every $\varepsilon\ge0$,
--   $$\mathbb P\{\lambda_{\max}(Y)\ge(1+\varepsilon)b\}\le d\left[\frac{e^\varepsilon}{(1+\varepsilon)^{1+\varepsilon}}\right]^{b/L}.$$
--   At $L=0$ both tail expressions are explicitly $d$; all summands then vanish almost surely. The family may be empty, and either mean eigenvalue may be zero. This goal retains every conclusion of the source theorem and the distinct lower- and upper-tail deviation domains.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 5.1.1, equations (5.1.1–6), printed p. 60.

import Definitions.Def_TroppMatrixConcentration_ch5_chernoff_functions

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem ch5_matrix_chernoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (X k)) (hIndep : iIndepFun X μ)
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (X k ω) ∧ lambdaMax (X k ω) ≤ L) :
    let Y := fun ω => ∑ k, X k ω
    let a := lambdaMin (∫ ω, Y ω ∂μ)
    let b := lambdaMax (∫ ω, Y ω ∂μ)
    a = lambdaMin (∑ k, ∫ ω, X k ω ∂μ) ∧
    b = lambdaMax (∑ k, ∫ ω, X k ω ∂μ) ∧
    (∀ θ : ℝ, 0 < θ →
      (1 - Real.exp (-θ)) / θ * a - L * Real.log d / θ ≤
        (∫ ω, lambdaMin (Y ω) ∂μ) ∧
      (∫ ω, lambdaMax (Y ω) ∂μ) ≤
        (Real.exp θ - 1) / θ * b + L * Real.log d / θ) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 →
      (μ {ω | lambdaMin (Y ω) ≤ (1 - ε) * a}).toReal ≤
        chernoffLowerTail d a L ε) ∧
    (∀ ε : ℝ, 0 ≤ ε →
      (μ {ω | (1 + ε) * b ≤ lambdaMax (Y ω)}).toReal ≤
        chernoffUpperTail d b L ε) := by sorry

end TroppMatrixConcentration
