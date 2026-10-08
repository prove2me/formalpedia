-- Prove2me | Theorems.Thm_ShorNonsmooth_Fejer_polyak_step_dist_sq_le
-- name    : ShorNonsmooth.Fejer.polyak_step_dist_sq_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:30:24.956983+00:00
-- url     : https://prove2.me/theorems/c1e5b79c-600f-4c00-905b-2dabb6316828
-- title:
--   Eq. (2.33) — a Polyak step strictly decreases the distance to every point of $M(c)$
-- statement:
--   Let $f$ be convex on $E_n$, $c \in \mathbb{R}$, $M(c) = \{x : f(x) \le c\}$, and $0 < \gamma < 2$. Let $x_k \notin M(c)$, let $g_k$ be a subgradient of $f$ at $x_k$, and set
--   $$
--   x_{k+1} = x_k - \frac{\gamma\,[f(x_k) - c]}{\|g_k\|^2}\, g_k .
--   $$
--   Then for every $y \in M(c)$
--   $$
--   \|x_{k+1} - y\|^2 \le \|x_k - y\|^2 - \gamma(2-\gamma)\,\frac{[f(x_k) - c]^2}{\|g_k\|^2} < \|x_k - y\|^2 .
--   $$
--
--   This is the Fejér inequality behind every result of the section: it says that Polyak's step is an $M(c)$-Fejér map, and it quantifies the decrease.
--
--   **Formalization Note** The step is written out with the single subgradient $g_k$; the hypotheses force $g_k \neq 0$ (a zero subgradient would make $x_k$ a minimum point, hence $x_k \in M(c)$), so the division is genuine.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 37, inequality (2.33) (proof of Theorem 2.11)

import Mathlib
import Definitions.Def_ShorNonsmooth_Fejer_PolyakMethod

open Filter Topology

namespace ShorNonsmooth.Fejer

/-- Shor (1985), p. 37, inequality (2.33) (proof of Theorem 2.11). Let `f` be convex on `E_n`,
`M(c) = {x : f(x) ≤ c}`, `0 < γ < 2`, and let `g_k` be a subgradient of `f` at `x_k ∉ M(c)`.
Then for every `y ∈ M(c)` the Polyak step `x_{k+1} = x_k - γ [f(x_k) - c] / ‖g_k‖² · g_k`
satisfies
`‖x_{k+1} - y‖² ≤ ‖x_k - y‖² - γ(2 - γ) [f(x_k) - c]² / ‖g_k‖² < ‖x_k - y‖²`. -/
theorem polyak_step_dist_sq_le {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (c γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (xk gk y : EuclideanSpace ℝ (Fin n)) (hgk : ShorNonsmooth.AlmostDiff.IsSubgradient f xk gk)
    (hxk : xk ∉ levelSet f c) (hy : y ∈ levelSet f c) :
    ‖xk - (γ * (f xk - c) / ‖gk‖ ^ 2) • gk - y‖ ^ 2 ≤
        ‖xk - y‖ ^ 2 - γ * (2 - γ) * (f xk - c) ^ 2 / ‖gk‖ ^ 2 ∧
      ‖xk - y‖ ^ 2 - γ * (2 - γ) * (f xk - c) ^ 2 / ‖gk‖ ^ 2 < ‖xk - y‖ ^ 2 := by sorry

end ShorNonsmooth.Fejer
