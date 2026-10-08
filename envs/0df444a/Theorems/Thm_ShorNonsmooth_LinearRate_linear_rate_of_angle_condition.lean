-- Prove2me | Theorems.Thm_ShorNonsmooth_LinearRate_linear_rate_of_angle_condition
-- name    : ShorNonsmooth.LinearRate.linear_rate_of_angle_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:02:42.855993+00:00
-- url     : https://prove2.me/theorems/3d987671-4f53-4253-a0ad-66b61b5fb2f4
-- title:
--   Theorem 2.7 — under the angle condition (2.12), geometric stepsizes give $\|x_k - x^*(x_k)\| \le h_{k+1}/\cos\varphi$ or $2h_{k+1}\cos\varphi$
-- statement:
--   Let $f$ be a convex function on $E_n$ with a nonempty set of minimum points $M^*$, and for $x \in E_n$ let $x^*(x)$ be the point of $M^*$ nearest to $x$. Let $g_f(x)$ be any subgradient of $f$ at $x$. Assume that for some angle $0 \le \varphi < \pi/2$ and all $x \in E_n$
--   $$
--   (g_f(x),\, x - x^*(x)) \ge \cos\varphi\, \|g_f(x)\|\, \|x - x^*(x)\|. \tag{2.12}
--   $$
--   Given $x_0$, choose $h_1 \ge \|x^*(x_0) - x_0\|\cos\varphi$ if $\pi/4 \le \varphi < \pi/2$ (2.13), and $h_1 \ge \|x^*(x_0) - x_0\|/(2\cos\varphi)$ if $0 \le \varphi < \pi/4$ (2.14); set $h_{k+1} = h_k\, r(\varphi)$ for $k = 1, 2, \dots$ with $r(\varphi) = \sin\varphi$, resp. $1/(2\cos\varphi)$ (2.15)–(2.16); and generate $x_{k+1} = x_k - h_{k+1} g_f(x_k)/\|g_f(x_k)\|$. Then for all $k = 0, 1, 2, \dots$
--   $$
--   \|x_k - x^*(x_k)\| \le \begin{cases} h_{k+1}/\cos\varphi, & \pi/4 \le \varphi < \pi/2, \quad (2.18) \\ 2h_{k+1}\cos\varphi, & 0 \le \varphi < \pi/4. \quad (2.19) \end{cases}
--   $$
--
--   If the angle $\varphi$ is known in advance, the method therefore converges to the set of minima with the speed of a geometric progression of ratio $r(\varphi)$.
--
--   **Formalization Note** The book states the conclusion as "either $g_f(x_{k^*}) = 0$ for some $k^*$, i.e. $x_{k^*}$ is a minimum point, or (2.18)/(2.19) hold for all $k$". In the formalization the method stops at such a point and stays there, where the distance to $M^*$ is $0$; the bound is then asserted for every $k$, which implies the book's alternative. The ratio is $1/(2\cos\varphi)$ where the page prints "1/2 cos φ" (see the definition). The stepsize recursion is required for $k \ge 1$ only; $h_1$ is the chosen initial step.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 30–31, Theorem 2.7, (2.12)–(2.19)

import Mathlib
import Definitions.Def_ShorNonsmooth_LinearRate_SubgradientMethod

namespace ShorNonsmooth.LinearRate

/-- Shor (1985), pp. 30–31, **Theorem 2.7**. Let `f` be convex on `E_n` with a nonempty set of
minima, and let `0 ≤ φ < π/2` be such that for all `x` (2.12) holds:
`(g_f(x), x - x*(x)) ≥ cos φ ‖g_f(x)‖ ‖x - x*(x)‖`, where `x*(x)` is the nearest minimum point.
If `h₁` satisfies (2.13)/(2.14) and `h_{k+1} = h_k r(φ)`, `k ≥ 1` (2.15)–(2.16), then the
normalized subgradient iterates satisfy (2.18) `‖x_k - x*(x_k)‖ ≤ h_{k+1}/cos φ` when
`π/4 ≤ φ`, and (2.19) `‖x_k - x*(x_k)‖ ≤ 2 h_{k+1} cos φ` when `φ < π/4`, for all `k`.
The book's alternative "`g_f(x_{k*}) = 0` for some `k*`" is the stop of the method; the
stopped sequence stays at that minimum point, where the bound holds trivially. -/
theorem linear_rate_of_angle_condition {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hMne : (ShorNonsmooth.SubgradMethod.MinSet f).Nonempty)
    (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < Real.pi / 2)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (hangle : ∀ x, inner ℝ (g x) (x - nearestMin f x) ≥
      Real.cos φ * ‖g x‖ * ‖x - nearestMin f x‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ)
    (hh₁_ge : Real.pi / 4 ≤ φ → ‖nearestMin f x₀ - x₀‖ * Real.cos φ ≤ h 1)
    (hh₁_lt : φ < Real.pi / 4 → ‖nearestMin f x₀ - x₀‖ / (2 * Real.cos φ) ≤ h 1)
    (hrec : ∀ k, 1 ≤ k → h (k + 1) = h k * stepRatio φ) :
    (Real.pi / 4 ≤ φ → ∀ k, ‖ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k - nearestMin f (ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k)‖
        ≤ h (k + 1) / Real.cos φ) ∧
    (φ < Real.pi / 4 → ∀ k, ‖ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k - nearestMin f (ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k)‖
        ≤ 2 * h (k + 1) * Real.cos φ) := by sorry

end ShorNonsmooth.LinearRate
