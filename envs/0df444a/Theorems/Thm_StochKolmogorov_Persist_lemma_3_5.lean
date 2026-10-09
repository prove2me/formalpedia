-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_lemma_3_5
-- name    : StochKolmogorov.Persist.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:18.731324+00:00
-- url     : https://prove2.me/theorems/8bddb3e6-ab16-4848-beb9-56ac988f5ac1
-- title:
--   Lemma 3.5, p. 15 — if 𝔼e^{θ₀Y} + 𝔼e^{−θ₀Y} ≤ K₁, the log-Laplace transform φ has φ′(0) = 𝔼Y and 0 ≤ φ″ ≤ K₂ on [0, θ₀/2), K₂ depending only on K₁
-- statement:
--   Let $\theta_0>0$ and $K_1$ be constants. There is $K_2>0$, depending only on $K_1$ (and the fixed $\theta_0$), with the following property. Let $Y$ be a real random variable on any probability space such that
--   $$\mathbb E\exp(\theta_0Y)+\mathbb E\exp(-\theta_0Y)\le K_1 .$$
--   Then the log-Laplace transform $\phi(\theta)=\ln\mathbb E\exp(\theta Y)$ is twice differentiable on $[0,\theta_0/2)$,
--   $$\frac{d\phi}{d\theta}(0)=\mathbb EY,\qquad 0\le\frac{d^2\phi}{d\theta^2}(\theta)\le K_2,\quad\theta\in[0,\theta_0/2).$$
--
--   In the proof of Proposition 4.1 the lemma is applied to $Y=G(T)$, the logarithmic increment of $V$, uniformly in the starting point and in $T$; the uniformity of $K_2$ is what makes the resulting Taylor bound uniform.
--
--   **Formalization Note** $\phi$ is Mathlib's cumulant generating function `cgf Y P`. The page says $K_2$ depends only on $K_1$, but the proof also uses the fixed $\theta_0$: for $Y=\pm1/\theta_0$ with equal probabilities, $K_1=2\cosh(1)$ while $\phi''(0)=1/\theta_0^2$. The corrected quantifier order chooses $K_2$ after $\theta_0,K_1$ and before the probability space and $Y$. The two exponential moments are assumed integrable (the hypothesis $\mathbb E\exp(\pm\theta_0Y)<\infty$ that the bound $\le K_1$ presupposes). "Twice differentiable at $\theta$" means $\phi$ and $\phi'$ are differentiable at $\theta$ (two-sided, including at $\theta=0$).
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 3.5, p. 15

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

/-- Lemma 3.5 (p. 15): if `𝔼 exp(θ₀Y) + 𝔼 exp(−θ₀Y) ≤ K₁`, the log-Laplace transform
`φ(θ) = ln 𝔼 exp(θY)` is twice differentiable on `[0, θ₀/2)`, `φ'(0) = 𝔼Y` and
`0 ≤ φ''(θ) ≤ K₂` there. The page says `K₂` depends only on `K₁`; the proof also needs the fixed
`θ₀`, as shown by `Y = ±1/θ₀`, whose variance is `1/θ₀²`. -/
theorem lemma_3_5 (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (K₁ : ℝ) :
    ∃ K₂ : ℝ, 0 < K₂ ∧ ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (Y : Ω' → ℝ),
      Integrable (fun ω => Real.exp (θ₀ * Y ω)) P' →
      Integrable (fun ω => Real.exp (-θ₀ * Y ω)) P' →
      ∫ ω, Real.exp (θ₀ * Y ω) ∂P' + ∫ ω, Real.exp (-θ₀ * Y ω) ∂P' ≤ K₁ →
        (∀ θ ∈ Set.Ico 0 (θ₀ / 2), DifferentiableAt ℝ (cgf Y P') θ ∧
          DifferentiableAt ℝ (deriv (cgf Y P')) θ) ∧
        deriv (cgf Y P') 0 = ∫ ω, Y ω ∂P' ∧
        ∀ θ ∈ Set.Ico 0 (θ₀ / 2),
          0 ≤ iteratedDeriv 2 (cgf Y P') θ ∧ iteratedDeriv 2 (cgf Y P') θ ≤ K₂ := by sorry

end StochKolmogorov.Persist
