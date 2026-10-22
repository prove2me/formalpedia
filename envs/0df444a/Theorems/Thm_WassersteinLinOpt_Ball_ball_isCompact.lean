-- Prove2me | Theorems.Thm_WassersteinLinOpt_Ball_ball_isCompact
-- name    : WassersteinLinOpt.Ball.ball_isCompact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T17:28:51.031978+00:00
-- url     : https://prove2.me/theorems/e5b73089-c92d-41b6-91e8-391d3da9bf4c
-- title:
--   Theorem 1 — weak compactness of the Wasserstein ball
-- statement:
--   Throughout, $(X,d)$ is a proper metric space (every closed ball is compact; such a space is complete and separable, hence Polish) with its Borel $\sigma$-algebra, and $p \ge 1$, $r > 0$ are real.
--
--   **Theorem 1 (Weak Compactness of Wasserstein Ball).** If $\nu\in\mathcal P(X)$ has a finite $p$-th moment, then the Wasserstein ball
--
--   $$\mathcal B_r(\nu)=\{\mu\in\mathcal P(X):W_p(\mu,\nu)\le r\}$$
--
--   is compact in the weak topology of $\mathcal P(X)$.
--
--   Compactness is what makes the existence results of Sections 4 and 5 possible.
--
--   **Formalization Note.** $\mathcal P(X)$ is Mathlib's `ProbabilityMeasure X` with its topology of convergence against bounded continuous functions, i.e. the paper's weak convergence (Definition 2). The paper's weak compactness is sequential (Definition 3); since $\mathcal P(X)$ is metrizable (p. 1120) the two notions agree, and the statement uses `IsCompact`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1109, Theorem 1

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_WassersteinLinOpt_Ball_HasFinitePthMoment

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- Theorem 1 (Weak Compactness of Wasserstein Ball), p. 1109. On a proper metric space, the
Wasserstein ball `𝓑_r(ν)` is compact in the weak topology of `𝒫(X)` whenever `ν` has a
finite `p`-th moment. -/
theorem ball_isCompact {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X)) :
    IsCompact (wassersteinBall p r ν) := by sorry

end WassersteinLinOpt.Ball
