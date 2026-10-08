-- Prove2me | Theorems.Thm_ShorNonsmooth_Fejer_polyak_linear_rate_sharp_minimum
-- name    : ShorNonsmooth.Fejer.polyak_linear_rate_sharp_minimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:30:58.921218+00:00
-- url     : https://prove2.me/theorems/44588c40-47db-4cf1-8787-c79c28e7b4b6
-- title:
--   Theorem 2.13 — Polyak's method contracts by the factor $q$ at a sharp minimum
-- statement:
--   Let $f$ be convex on $E_n$ with a minimum point $x^*$, let $m > 0$ be such that
--   $$
--   f(x) - f(x^*) \ge m\,\|x - x^*\| \qquad \text{for all } x ,
--   $$
--   and let $L$ bound the norm of every subgradient of $f$ at every point of the ball $\|x - x^*\| \le \|x_0 - x^*\|$. Let $0 < \gamma < 2$ and let $\{x_k\}$ be generated from $x_0$ by Polyak's method (2.32) with $c = f(x^*)$, for any subgradient selection $g_f$. Then for every $k$
--   $$
--   \|x_{k+1} - x^*\| \le q\, \|x_k - x^*\|, \qquad q = \Bigl(1 - \gamma(2-\gamma)\frac{m^2}{L^2}\Bigr)^{1/2} .
--   $$
--
--   At a sharp minimum Polyak's step converges linearly without any smoothness.
--
--   **Formalization Note** The book assumes "$L$ the Lipschitz constant of $f$ in the area $\|x - x^*\| \le \|x_0 - x^*\|$", and its proof uses $\|g_f(x_k)\| \le L$. A Lipschitz constant on the closed ball does not bound subgradients at boundary points of the ball, and the per-step inequality then fails (e.g. $f(x) = m|x|$ on $[-1,1]$ with a steeper slope outside, $x^* = 0$, $x_0 = 1$). The statement therefore assumes the subgradient bound the proof uses; it holds whenever $f$ is $L$-Lipschitz on an open neighbourhood of the ball. The range $0 < \gamma < 2$ is the section's standing range.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 38, Theorem 2.13 (proof p. 39)

import Mathlib
import Definitions.Def_ShorNonsmooth_Fejer_PolyakMethod

open Filter Topology

namespace ShorNonsmooth.Fejer

/-- Shor (1985), p. 38, Theorem 2.13. Let `f` be convex on `E_n` with a minimum point `x*`, let
`m > 0` be such that `f(x) - f(x*) ≥ m ‖x - x*‖` for all `x`, and let `L` bound the norm of every
subgradient of `f` at every point of the ball `‖x - x*‖ ≤ ‖x₀ - x*‖` (the book: "`L` the Lipschitz
constant of `f` in the area `‖x - x*‖ ≤ ‖x₀ - x*‖`"; see the note below). Then Polyak's method
(2.32) with `c = f(x*)` and `0 < γ < 2`, for any subgradient selection, satisfies
`‖x_{k+1} - x*‖ ≤ q ‖x_k - x*‖` for all `k`, where `q = (1 - γ(2 - γ) m² / L²)^{1/2}`.

Note: the hypothesis is the bound `‖g‖ ≤ L` that the book's proof uses; a Lipschitz constant of
`f` on the closed ball alone does not bound subgradients at boundary points of the ball, and the
per-step inequality can then fail. -/
theorem polyak_linear_rate_sharp_minimum {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xstar : EuclideanSpace ℝ (Fin n))
    (hmin : ∀ y, f xstar ≤ f y) (m L : ℝ) (hm : 0 < m)
    (hsharp : ∀ x, f x - f xstar ≥ m * ‖x - xstar‖)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : ∀ k, x (k + 1) = polyakStep f g (f xstar) γ (x k))
    (hL : ∀ z ∈ Metric.closedBall xstar ‖x 0 - xstar‖, ∀ v, ShorNonsmooth.AlmostDiff.IsSubgradient f z v → ‖v‖ ≤ L) :
    ∀ k : ℕ, ‖x (k + 1) - xstar‖ ≤
      Real.sqrt (1 - γ * (2 - γ) * m ^ 2 / L ^ 2) * ‖x k - xstar‖ := by sorry

end ShorNonsmooth.Fejer
