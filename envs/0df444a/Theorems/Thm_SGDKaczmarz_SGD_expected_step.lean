-- Prove2me | Theorems.Thm_SGDKaczmarz_SGD_expected_step
-- name    : SGDKaczmarz.SGD.expected_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:24.376353+00:00
-- url     : https://prove2.me/theorems/78f8f310-c967-4dd3-8748-becba43c833f
-- title:
--   Proof of Theorem 2.1, pp. 22–23 — E‖x_{k+1} − x⋆‖² ≤ (1 − 2γµ(1 − γ sup L))‖x_k − x⋆‖² + 2γ²σ² for γ ≤ 1/sup L
-- statement:
--   Work in the setting of Theorem 2.1: $\mathcal D$ is a probability distribution on an index space $I$; $\mathcal H$ is a separable real Hilbert space; each $f_i : \mathcal H \to \mathbb R$ is convex and differentiable, with $\nabla f_i$ Lipschitz with constant $L_i$ and $L_i \le \sup L$ almost surely; $F(x) = \mathbb E f_i(x)$ is finite for every $x$ and $i \mapsto \nabla f_i(x)$ is measurable; $F$ is $\mu$-strongly convex with $\mu > 0$ in the sense of assumption (2),
--   $$\langle x - y, \nabla F(x) - \nabla F(y)\rangle \ge \mu\|x - y\|_2^2 \quad\text{for all } x, y;$$
--   $x_\star$ minimizes $F$; and $\sigma^2 = \mathbb E\|\nabla f_i(x_\star)\|_2^2 \in [0,\infty]$.
--
--   Let $0 < \gamma \le 1/\sup L$ and fix the current iterate $x_k \in \mathcal H$. If the next iterate is $x_{k+1} = x_k - \gamma\nabla f_i(x_k)$ with $i \sim \mathcal D$, then
--   $$\mathbb E\|x_{k+1} - x_\star\|_2^2 \le \bigl(1 - 2\gamma\mu(1 - \gamma\sup L)\bigr)\|x_k - x_\star\|_2^2 + 2\gamma^2\sigma^2,$$
--   the expectation being over $i$ only.
--
--   This is the expected one-step recursion of the proof of Theorem 2.1; iterating it gives the theorem.
--
--   **Formalization Note** The expectation of the nonnegative quantity $\|x_{k+1} - x_\star\|^2$ is a lower Lebesgue integral in $[0,\infty]$, so the left side is never a junk value; when $\sigma^2 = \infty$ the right side is $\infty$. The condition $\gamma \le 1/\sup L$ is written $\gamma\cdot\sup L \le 1$, and $\sup L$ may be any almost-sure upper bound of $L_i$ (the bound is increasing in $\sup L$). $F$ is not assumed differentiable separately: assumption (2) is stated for Mathlib's `gradient` of $F$, and $F$ is differentiable whenever $\sigma^2 < \infty$.
-- source:
--   Needell, Srebro & Ward, Stochastic gradient descent, weighted sampling, and the randomized Kaczmarz algorithm, arXiv:1310.5715v5, proof of Theorem 2.1 (Appendix A.2), second display, pp. 22–23

import Mathlib
import Definitions.Def_SGDKaczmarz_SGD_Setting

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace SGDKaczmarz.SGD

/-- Proof of Theorem 2.1 (Appendix A.2), pp. 22–23: the expected one-step recursion. For a fixed
current iterate `x = x_k` and `γ ≤ 1/sup L`, the expectation over the index `i ∼ 𝒟` drawn at step `k`
satisfies `E‖x_{k+1} − x⋆‖² ≤ (1 − 2γμ(1 − γ sup L))‖x_k − x⋆‖² + 2γ²σ²`. -/
theorem expected_step {I : Type*} [MeasurableSpace I] (D : Measure I) [IsProbabilityMeasure D]
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
    (γ : ℝ) (hγ : 0 < γ) (hγL' : γ * supL ≤ 1) (x : H) :
    ∫⁻ i, ENNReal.ofReal (‖x - xstar - γ • gradient (f i) x‖ ^ 2) ∂D
      ≤ ENNReal.ofReal ((1 - 2 * γ * μ * (1 - γ * supL)) * ‖x - xstar‖ ^ 2)
        + ENNReal.ofReal (2 * γ ^ 2) * residual D f xstar := by sorry

end SGDKaczmarz.SGD
