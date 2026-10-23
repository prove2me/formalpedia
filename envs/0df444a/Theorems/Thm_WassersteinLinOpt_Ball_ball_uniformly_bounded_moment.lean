-- Prove2me | Theorems.Thm_WassersteinLinOpt_Ball_ball_uniformly_bounded_moment
-- name    : WassersteinLinOpt.Ball.ball_uniformly_bounded_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T17:13:02.612788+00:00
-- url     : https://prove2.me/theorems/b635b1fe-a523-4227-b1b0-c24822a18ac5
-- title:
--   Lemma 1 — the Wasserstein ball has a uniformly bounded $p$-th moment
-- statement:
--   Throughout, $(X,d)$ is a proper metric space (every closed ball is compact; such a space is complete and separable, hence Polish) with its Borel $\sigma$-algebra, and $p \ge 1$, $r > 0$ are real.
--
--   **Lemma 1.** Let $\nu\in\mathcal P(X)$ have a finite $p$-th moment. Then for every $x_0\in X$ there is a constant $C>0$ such that
--
--   $$\int_X d^p(x,x_0)\,d\mu(x)\le C\qquad\text{for all }\mu\in\mathcal B_r(\nu).$$
--
--   In particular every measure in the ball has a finite $p$-th moment. The lemma feeds the tightness argument of Theorem 1 and the truncation estimate of Theorem 3.
--
--   **Formalization Note.** The paper leaves $x_0$ free; the statement is given for every $x_0$ (the choice does not matter, p. 1109), which is the form Theorem 3's proof uses. $C$ is only asserted to exist; it may depend on $p$, $r$, $\nu$ and $x_0$. The moment is a lower Lebesgue integral in `ℝ≥0∞`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1109, Lemma 1

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_WassersteinLinOpt_Ball_HasFinitePthMoment

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- Lemma 1 (Yue–Kuhn–Wiesemann 2022, p. 1109). If `ν` has a finite `p`-th moment, then the
Wasserstein ball `𝓑_r(ν)` has a uniformly bounded `p`-th moment: for every reference point
`x₀` there is `C > 0` with `∫_X d^p(x, x₀) dμ(x) ≤ C` for all `μ ∈ 𝓑_r(ν)`. -/
theorem ball_uniformly_bounded_moment {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X)) (x₀ : X) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ ∈ wassersteinBall p r ν,
      ∫⁻ x, ENNReal.ofReal (dist x x₀ ^ p) ∂(μ : Measure X) ≤ ENNReal.ofReal C := by sorry

end WassersteinLinOpt.Ball
