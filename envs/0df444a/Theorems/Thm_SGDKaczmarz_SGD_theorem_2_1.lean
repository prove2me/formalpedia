-- Prove2me | Theorems.Thm_SGDKaczmarz_SGD_theorem_2_1
-- name    : SGDKaczmarz.SGD.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:13.788928+00:00
-- url     : https://prove2.me/theorems/e95c45da-3c4a-427c-9f93-4ab3ef0981ee
-- title:
--   Theorem 2.1, (2.4), p. 4 — E‖x_k − x⋆‖² ≤ [1 − 2γµ(1 − γ sup L)]^k ‖x_0 − x⋆‖² + γσ²/(µ(1 − γ sup L)) for γ < 1/sup L
-- statement:
--   Let $\mathcal D$ be a probability distribution (the source distribution) on an arbitrary measurable index space $I$, and let $\mathcal H$ be a separable real Hilbert space. Let $f_i : \mathcal H \to \mathbb R$, $i \in I$, satisfy:
--
--   1. each $f_i$ is convex and differentiable, and $\nabla f_i$ has Lipschitz constant $L_i$, with $L_i \le \sup L$ almost surely;
--   2. $F(x) = \mathbb E f_i(x)$ is finite for every $x$, and $i \mapsto \nabla f_i(x)$ is measurable for every $x$;
--   3. $F$ is $\mu$-strongly convex, $\mu > 0$: $\langle x - y, \nabla F(x) - \nabla F(y)\rangle \ge \mu\|x - y\|_2^2$ for all $x, y$.
--
--   Let $x_\star$ minimize $F$ and set $\sigma^2 = \mathbb E\|\nabla f_i(x_\star)\|_2^2 \in [0,\infty]$. Let $0 < \gamma < 1/\sup L$, let $x_0 \in \mathcal H$, and let $x_{k+1} = x_k - \gamma\nabla f_{i_k}(x_k)$ be the SGD iterates (2.2), with $\{i_k\}$ drawn i.i.d. from $\mathcal D$. Then for every $k \ge 0$
--   $$\mathbb E\|x_k - x_\star\|_2^2 \le \Bigl[1 - 2\gamma\mu(1 - \gamma\sup L)\Bigr]^k\|x_0 - x_\star\|_2^2 + \frac{\gamma\sigma^2}{\mu(1 - \gamma\sup L)},$$
--   where the expectation is with respect to the sampling of $\{i_k\}$.
--
--   This is the main theorem of the paper: SGD with a fixed step converges linearly to a neighbourhood of $x_\star$ whose radius is proportional to $\gamma\sigma^2$, with a rate governed by the uniform conditioning $\sup L/\mu$. Corollary 2.2 and the importance-sampling and Kaczmarz corollaries of Sections 3 and 5 are obtained from it.
--
--   **Formalization Note** The expectation of $\|x_k - x_\star\|^2$ and $\sigma^2$ are lower Lebesgue integrals in $[0,\infty]$ over the infinite product law of $\{i_k\}$ and over $\mathcal D$, so a non-integrable iterate cannot satisfy the bound vacuously; when $\sigma^2 = \infty$ the right side is $\infty$, which is the paper's meaning. The condition $\gamma < 1/\sup L$ is written $\gamma\cdot\sup L < 1$ (equivalent for $\sup L > 0$, and the page's $1/0 = \infty$ for $\sup L = 0$). The page defines $\sup L$ as the essential supremum of $L_i$ and uses it only through "$L_i \le \sup L$ a.s."; the theorem is stated for every almost-sure upper bound, which is equivalent because the bound is increasing in $\sup L$. Integrability of $f_i(x)$, measurability of $\nabla f_i(x)$ in $i$ and separability of $\mathcal H$ are what make $F$ and the iterates' expectation meaningful. Assumption (2) is stated for Mathlib's `gradient` of $F$.
-- source:
--   Needell, Srebro & Ward, Stochastic gradient descent, weighted sampling, and the randomized Kaczmarz algorithm, arXiv:1310.5715v5, Theorem 2.1, (2.4), p. 4

import Mathlib
import Definitions.Def_SGDKaczmarz_SGD_Setting

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace SGDKaczmarz.SGD

/-- Theorem 2.1, (2.4), p. 4 (Needell–Srebro–Ward, arXiv:1310.5715v5): for `γ < 1/sup L` the SGD
iterates (2.2) satisfy
`E‖x_k − x⋆‖² ≤ [1 − 2γμ(1 − γ sup L)]^k ‖x_0 − x⋆‖² + γσ²/(μ(1 − γ sup L))`, the expectation being
over the i.i.d. sampling of `{i_k}`. -/
theorem theorem_2_1 {I : Type*} [MeasurableSpace I] (D : Measure I) [IsProbabilityMeasure D]
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
    (γ : ℝ) (hγ : 0 < γ) (hγL : γ * supL < 1) (x0 : H) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖sgdIter f γ x0 k ω - xstar‖ ^ 2) ∂(iidLaw D)
      ≤ ENNReal.ofReal ((1 - 2 * γ * μ * (1 - γ * supL)) ^ k * ‖x0 - xstar‖ ^ 2)
        + ENNReal.ofReal (γ / (μ * (1 - γ * supL))) * residual D f xstar := by sorry

end SGDKaczmarz.SGD
