-- Prove2me | Theorems.Thm_ShorNonsmooth_LinearRate_angle_condition_of_level_set_ratio
-- name    : ShorNonsmooth.LinearRate.angle_condition_of_level_set_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:02:53.699121+00:00
-- url     : https://prove2.me/theorems/fc6840cf-2611-453b-8da1-cf45f66c9b49
-- title:
--   Eq. (2.22) — the level-surface ratio condition (2.20) gives $(g_f(x), x - x^*) \ge \frac1\sigma\|g_f(x)\|\|x - x^*\|$
-- statement:
--   Let $f$ be a convex function on $E_n$ with a unique minimum point $x^*$. Let $\sigma \ge \sqrt2$ and $h_1 \ge 0$, let $Y = \{y : \|y - x^*\| \le \sigma h_1\}$, and assume that every pair of points $x, z \in Y$ with $f(x) = f(z) \ne f(x^*)$ satisfies
--   $$
--   \|x - x^*\| \le \sigma\, \|z - x^*\|. \tag{2.20}
--   $$
--   Then for every $x \in Y$ and every subgradient $g$ of $f$ at $x$,
--   $$
--   (g,\, x - x^*) \ge \frac{1}{\sigma}\, \|g\|\, \|x - x^*\|. \tag{2.22}
--   $$
--
--   Condition (2.20) bounds how oblong the level surfaces of $f$ are near $x^*$; (2.22) converts it into the angle condition (2.12) of Theorem 2.7 with $\cos\varphi = 1/\sigma$, which is how Theorem 2.8 is reduced to Theorem 2.7.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 32–33, proof of Theorem 2.8, inequality (2.22)

import Mathlib
import Definitions.Def_ShorNonsmooth_LinearRate_SubgradientMethod

namespace ShorNonsmooth.LinearRate

/-- Shor (1985), pp. 32–33, inequality (2.22) in the proof of Theorem 2.8. Let `f` be convex on
`E_n` with unique minimum point `x*`, let `σ ≥ √2`, `h₁ ≥ 0`, `Y = {y : ‖y - x*‖ ≤ σ h₁}`, and
assume (2.20): `‖x - x*‖ ≤ σ ‖z - x*‖` for all `x, z ∈ Y` with `f(x) = f(z) ≠ f(x*)`. Then for
every `x ∈ Y` and every subgradient `g` of `f` at `x`,
`(g, x - x*) ≥ (1/σ) ‖g‖ ‖x - x*‖`. -/
theorem angle_condition_of_level_set_ratio {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xs : EuclideanSpace ℝ (Fin n)) (hxs : ShorNonsmooth.SubgradMethod.MinSet f = {xs})
    (σ h₁ : ℝ) (hσ : Real.sqrt 2 ≤ σ) (hh₁ : 0 ≤ h₁)
    (hY : ∀ x ∈ Metric.closedBall xs (σ * h₁), ∀ z ∈ Metric.closedBall xs (σ * h₁),
      f x = f z → f x ≠ f xs → ‖x - xs‖ ≤ σ * ‖z - xs‖)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.closedBall xs (σ * h₁))
    (gx : EuclideanSpace ℝ (Fin n)) (hgx : ShorNonsmooth.AlmostDiff.IsSubgradient f x gx) :
    inner ℝ gx (x - xs) ≥ (1 / σ) * ‖gx‖ * ‖x - xs‖ := by sorry

end ShorNonsmooth.LinearRate
