-- Prove2me | Theorems.Thm_WassersteinLinOpt_Ball_optimalValue_finite_iff_growth
-- name    : WassersteinLinOpt.Ball.optimalValue_finite_iff_growth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T18:09:40.708552+00:00
-- url     : https://prove2.me/theorems/4dafc612-5a47-4776-9800-87be013e8379
-- title:
--   Theorem 2 — the optimal value of (3) is finite iff $f$ has $p$-growth
-- statement:
--   Throughout, $(X,d)$ is a proper metric space (every closed ball is compact; such a space is complete and separable, hence Polish) with its Borel $\sigma$-algebra, and $p \ge 1$, $r > 0$ are real. Standing assumptions of problem (3) (p. 1108): $f$ is upper semicontinuous and, for every $\mu \in \mathcal B_r(\nu)$, at least one of $\int_X [f]_+\,d\mu$ and $\int_X [-f]_+\,d\mu$ is finite.
--
--   **Theorem 2.** Assume $\nu$ has a finite $p$-th moment. Then the optimal value
--
--   $$\sup\Big\{\int_X f\,d\mu:\mu\in\mathcal B_r(\nu)\Big\}$$
--
--   of problem (3) is finite (neither $+\infty$ nor $-\infty$) if and only if there exist $x_0\in X$ and $c>0$ such that $f(x)\le c\,[1+d^p(x,x_0)]$ for all $x\in X$.
--
--   **Formalization Note.** The integral is the extended-real integral $\int[f]_+d\mu-\int[-f]_+d\mu$ (`quasiIntegral`) and the supremum is in `EReal`; "finite" is `≠ ⊤ ∧ ≠ ⊥`. The standing quasi-integrability assumption is the hypothesis `hquasi`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1110, Theorem 2

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_WassersteinLinOpt_Ball_HasFinitePthMoment
import Definitions.Def_WassersteinLinOpt_Ball_optimalValue

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- Theorem 2, p. 1110. Let `f` be upper semicontinuous and, for every `μ ∈ 𝓑_r(ν)`, let at
least one of `∫ [f]₊ dμ`, `∫ [−f]₊ dμ` be finite (the standing assumptions of problem (3)).
If `ν` has a finite `p`-th moment, the optimal value of (3) is finite (neither `+∞` nor `−∞`)
iff `f(x) ≤ c[1 + d^p(x, x₀)]` for all `x`, for some `x₀ ∈ X` and `c > 0`. -/
theorem optimalValue_finite_iff_growth {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (hf : UpperSemicontinuous f)
    (hquasi : ∀ μ ∈ wassersteinBall p r ν,
      ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) < ⊤ ∨
        ∫⁻ x, ENNReal.ofReal (-f x) ∂(μ : Measure X) < ⊤) :
    (optimalValue p r ν f ≠ ⊤ ∧ optimalValue p r ν f ≠ ⊥) ↔
      ∃ x₀ : X, ∃ c : ℝ, 0 < c ∧ ∀ x : X, f x ≤ c * (1 + dist x x₀ ^ p) := by sorry

end WassersteinLinOpt.Ball
