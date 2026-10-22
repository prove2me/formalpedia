-- Prove2me | Theorems.Thm_SimplexProj_Condat_entry_minus_radius_le_threshold
-- name    : SimplexProj.Condat.entry_minus_radius_le_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T23:37:45.196828+00:00
-- url     : https://prove2.me/theorems/5aaea52c-260f-4661-ab82-57ad222a0d6e
-- title:
--   Sect. 3 (p. 7) — for every $n$, $y_n - a \le \tau$
-- statement:
--   Let $N \ge 1$, $a > 0$, $y \in \mathbb{R}^N$, let $x = P_\Delta(y)$ be the Euclidean projection of $y$ onto the simplex of radius $a$, and let $\tau$ be the threshold of Proposition 2.2, so $x_n = \max\{y_n - \tau, 0\}$ for all $n$. Then
--
--   $$y_n - a \le \tau \qquad \text{for every } n = 1, \dots, N.$$
--
--   This is the lower bound behind the reset $\rho := y_n - a$ in step 2.3 of Condat's algorithm: when $y_n - a$ exceeds the current lower bound $\rho$ of $\tau$, it replaces it.
--
--   **Formalization Note.** $x = P_\Delta(y)$ is the predicate `IsSimplexProjection a y x`.
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 7, Sect. 3 (sentence begun on p. 6)

import Mathlib
import Definitions.Def_SimplexProj_Condat_IsSimplexProjection

namespace SimplexProj.Condat

/-- Condat, Sect. 3, pp. 6–7: for every `n`, `y_n - a ≤ τ`, where `τ` is the threshold of
Proposition 2.2 (`x = P_Δ(y)`, `x_n = max {y_n - τ, 0}`). Standing assumptions of p. 1:
`N ≥ 1`, `a > 0`. -/
theorem entry_minus_radius_le_threshold (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a)
    (y x : Fin N → ℝ) (hx : IsSimplexProjection a y x)
    (τ : ℝ) (hτ : ∀ n, x n = max (y n - τ) 0) :
    ∀ n, y n - a ≤ τ := by sorry

end SimplexProj.Condat
