-- Prove2me | Theorems.Thm_SGDKaczmarz_SGD_unrolled_recursion
-- name    : SGDKaczmarz.SGD.unrolled_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:41.804376+00:00
-- url     : https://prove2.me/theorems/afcb9606-7a21-49dc-a1c2-c67d2f4107cb
-- title:
--   Proof of Theorem 2.1, p. 23 — E‖x_k − x⋆‖² ≤ (1 − 2γµ(1 − γ sup L))^k ‖x₀ − x⋆‖² + 2Σ_{j<k}(1 − 2γµ(1 − γ sup L))^j γ²σ²
-- statement:
--   Work in the setting of Theorem 2.1 (see the expected one-step recursion): $\mathcal D$, $\mathcal H$, convex differentiable components $f_i$ with $L_i$-Lipschitz gradients and $L_i \le \sup L$ almost surely, the objective $F = \mathbb E f_i$, $\mu$-strongly convex with $\mu > 0$, a minimizer $x_\star$ of $F$ and the residual $\sigma^2 = \mathbb E\|\nabla f_i(x_\star)\|_2^2 \in [0,\infty]$. Let $0 < \gamma \le 1/\sup L$, let $x_0 \in \mathcal H$, and let $x_k$ be the SGD iterates (2.2) driven by an i.i.d. sequence $\{i_k\}$ with law $\mathcal D$. Write $q = 1 - 2\gamma\mu(1 - \gamma\sup L)$. Then for every $k \ge 0$
--   $$\mathbb E\|x_k - x_\star\|_2^2 \le q^k\|x_0 - x_\star\|_2^2 + 2\sum_{j=0}^{k-1} q^j\gamma^2\sigma^2,$$
--   the expectation being over the sampling of $\{i_k\}$.
--
--   This is the first inequality of the last display of the proof of Theorem 2.1, obtained by applying the one-step recursion over the first $k$ iterations; summing the geometric series gives (2.4).
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$ with respect to the infinite product law of $\{i_k\}$; the iterate $x_k$ is a function of $i_0, \dots, i_{k-1}$. The empty sum at $k = 0$ is $0$. The conventions on $\gamma\cdot\sup L \le 1$ and on $\sup L$ are those of the one-step recursion.
-- source:
--   Needell, Srebro & Ward, Stochastic gradient descent, weighted sampling, and the randomized Kaczmarz algorithm, arXiv:1310.5715v5, proof of Theorem 2.1 (Appendix A.2), last display, first inequality, p. 23

import Mathlib
import Definitions.Def_SGDKaczmarz_SGD_Setting

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace SGDKaczmarz.SGD

/-- Proof of Theorem 2.1 (Appendix A.2), p. 23, first inequality: recursively applying the one-step
bound over the first `k` iterations, for `γ ≤ 1/sup L`,
`E‖x_k − x⋆‖² ≤ (1 − 2γμ(1 − γ sup L))^k ‖x_0 − x⋆‖² + 2 Σ_{j<k} (1 − 2γμ(1 − γ sup L))^j γ²σ²`. -/
theorem unrolled_recursion {I : Type*} [MeasurableSpace I] (D : Measure I) [IsProbabilityMeasure D]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (f : I → H → ℝ) (L : I → ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hint : ∀ x, Integrable (fun i => f i x) D)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (μ : ℝ) (hμ : 0 < μ)
    (hF : ∀ x y, μ * ‖x - y‖ ^ 2 ≤
      ⟪x - y, gradient (objective D f) x - gradient (objective D f) y⟫_ℝ)
    (xstar : H) (hxstar : ∀ x, objective D f xstar ≤ objective D f x)
    (γ : ℝ) (hγ : 0 < γ) (hγL' : γ * supL ≤ 1) (x0 : H) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖sgdIter f γ x0 k ω - xstar‖ ^ 2) ∂(iidLaw D)
      ≤ ENNReal.ofReal ((1 - 2 * γ * μ * (1 - γ * supL)) ^ k * ‖x0 - xstar‖ ^ 2)
        + ENNReal.ofReal (2 * ∑ j ∈ Finset.range k, (1 - 2 * γ * μ * (1 - γ * supL)) ^ j * γ ^ 2)
          * residual D f xstar := by sorry

end SGDKaczmarz.SGD
