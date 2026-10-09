-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch7_intrinsic_chernoff
-- name    : TroppMatrixConcentration.ch7_intrinsic_chernoff
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:52:28.424484+00:00
-- url     : https://prove2.me/theorems/be5e3da7-d499-4cda-8a25-bf9df7c9c1a9
-- title:
--   Theorem 7.2.1 — Intrinsic matrix Chernoff
-- statement:
--   Let $X_k$ be a finite independent family of measurable positive semidefinite complex $d\times d$ random matrices, $d\ge1$, satisfying $\lambda_{\max}(X_k)\le L$ almost surely, with $L>0$. Set $Y=\sum_kX_k$. Let $M\ne0$ be a semidefinite upper bound for $\mathbb EY$, and put $r=r(M)$ and $a=\lambda_{\max}(M)$. Then for every $\theta>0$,
--   $$\mathbb E\lambda_{\max}(Y)\le\frac{e^\theta-1}{\theta}a+\frac L\theta\log(2r).$$
--   For every $\varepsilon\ge L/a$,
--   $$\mathbb P\{\lambda_{\max}(Y)\ge(1+\varepsilon)a\}\le2r\left[\frac{e^\varepsilon}{(1+\varepsilon)^{1+\varepsilon}}\right]^{a/L}.$$
--   Lean writes the bracketed power as $\exp((a/L)(\varepsilon-(1+\varepsilon)\log(1+\varepsilon)))$, an equal expression on this domain. The nonzero proxy ensures $a>0$. Both expectation and tail conclusions of the source are included; there is no lower-tail claim. The family may be empty.
--
--   The displayed expectation identity $\mathbb E Y=\sum_k\mathbb E X_k$ is also an explicit conclusion.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 7.2.1, equations (7.2.1–2), printed pp. 106–107; standing independence confirmed in proof, Section 7.6, printed p. 113.

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch7_intrinsic_chernoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ)
    (L : ℝ) (hL : 0 < L) (M : Matrix (Fin d) (Fin d) ℂ) (hM : M ≠ 0)
    (hMeas : ∀ k, Measurable (X k)) (hIndep : iIndepFun X μ)
    (hPSD : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (X k ω) ≤ L)
    (hMeanBound : loewnerLE (∫ ω, ∑ k, X k ω ∂μ) M) :
    let Y := fun ω => ∑ k, X k ω
    let r := intrinsicDimension M
    let a := lambdaMax M
    (∫ ω, Y ω ∂μ) = ∑ k, ∫ ω, X k ω ∂μ ∧
    (∀ θ : ℝ, 0 < θ → (∫ ω, lambdaMax (Y ω) ∂μ) ≤
      (Real.exp θ - 1) / θ * a + L / θ * Real.log (2 * r)) ∧
    ∀ ε : ℝ, L / a ≤ ε →
      (μ {ω | (1 + ε) * a ≤ lambdaMax (Y ω)}).toReal ≤
        2 * r * Real.exp (a / L * (ε - (1 + ε) * Real.log (1 + ε))) := by sorry

end TroppMatrixConcentration
