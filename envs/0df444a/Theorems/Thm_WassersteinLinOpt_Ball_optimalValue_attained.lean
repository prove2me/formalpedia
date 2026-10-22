-- Prove2me | Theorems.Thm_WassersteinLinOpt_Ball_optimalValue_attained
-- name    : WassersteinLinOpt.Ball.optimalValue_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T19:56:21.429677+00:00
-- url     : https://prove2.me/theorems/7b40f741-1a77-4683-b753-f9b32ac8aadf
-- title:
--   Theorem 3 — the optimal value of (3) is attained under $p'$-growth, $p'<p$
-- statement:
--   Throughout, $(X,d)$ is a proper metric space (every closed ball is compact; such a space is complete and separable, hence Polish) with its Borel $\sigma$-algebra, and $p \ge 1$, $r > 0$ are real. Standing assumptions of problem (3) (p. 1108): $f$ is upper semicontinuous and, for every $\mu \in \mathcal B_r(\nu)$, at least one of $\int_X [f]_+\,d\mu$ and $\int_X [-f]_+\,d\mu$ is finite.
--
--   **Theorem 3.** Assume $\nu$ has a finite $p$-th moment. If there exist $x_0\in X$, $c>0$ and $p'\in(0,p)$ such that
--
--   $$f(x)\le c\,[1+d^{p'}(x,x_0)]\qquad\text{for all }x\in X,$$
--
--   then the optimal value of problem (3) is attained: some $\mu^\star\in\mathcal B_r(\nu)$ satisfies $\int_X f\,d\mu^\star=\sup\{\int_X f\,d\mu:\mu\in\mathcal B_r(\nu)\}$.
--
--   Compared with Theorem 2, the growth exponent must be strictly smaller than $p$; the paper points to an instance with growth exponent exactly $p$ where the value is finite but not attained.
--
--   **Formalization Note.** "Attained" is membership in the ball together with equality of the `EReal` values `quasiIntegral f μ = optimalValue p r ν f`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1112, Theorem 3

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_WassersteinLinOpt_Ball_HasFinitePthMoment
import Definitions.Def_WassersteinLinOpt_Ball_optimalValue

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- Theorem 3, p. 1112. Under the standing assumptions of problem (3) (`f` upper
semicontinuous, quasi-integrable under every `μ ∈ 𝓑_r(ν)`), if `ν` has a finite `p`-th moment
and `f(x) ≤ c[1 + d^{p′}(x, x₀)]` for all `x`, for some `x₀ ∈ X`, `c > 0` and `p′ ∈ (0, p)`, then
the optimal value of (3) is attained by some `μ⋆ ∈ 𝓑_r(ν)`. -/
theorem optimalValue_attained {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (hf : UpperSemicontinuous f)
    (hquasi : ∀ μ ∈ wassersteinBall p r ν,
      ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) < ⊤ ∨
        ∫⁻ x, ENNReal.ofReal (-f x) ∂(μ : Measure X) < ⊤)
    (x₀ : X) (c p' : ℝ) (hc : 0 < c) (hp'0 : 0 < p') (hp'p : p' < p)
    (hgrowth : ∀ x : X, f x ≤ c * (1 + dist x x₀ ^ p')) :
    ∃ μ ∈ wassersteinBall p r ν,
      quasiIntegral f (μ : Measure X) = optimalValue p r ν f := by sorry

end WassersteinLinOpt.Ball
