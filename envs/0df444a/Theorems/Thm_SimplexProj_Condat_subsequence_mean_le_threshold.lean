-- Prove2me | Theorems.Thm_SimplexProj_Condat_subsequence_mean_le_threshold
-- name    : SimplexProj.Condat.subsequence_mean_le_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T23:32:21.222988+00:00
-- url     : https://prove2.me/theorems/77ab2d46-1469-4cd5-bc16-b5e774e3855c
-- title:
--   Sect. 2 (p. 5) — every subsequence value $(\sum_{y\in v} y - a)/|v|$ is a lower bound of $\tau$
-- statement:
--   Let $N \ge 1$, $a > 0$, $y \in \mathbb{R}^N$, let $x = P_\Delta(y)$ be the Euclidean projection of $y$ onto the simplex of radius $a$, and let $\tau$ be the threshold of Proposition 2.2, so $x_n = \max\{y_n - \tau, 0\}$ for all $n$. Then for every subsequence $v$ of $y$, i.e. every nonempty set $S$ of indices,
--
--   $$\frac{\sum_{n \in S} y_n - a}{|S|} \le \tau.$$
--
--   This is the lower bound that Michelot's method and Condat's algorithm maintain: the running value $\rho = (\sum_{y \in v} y - a)/|v|$ never exceeds $\tau$, which justifies discarding every entry $y \le \rho$.
--
--   **Formalization Note.** A subsequence of $y$ is represented by its nonempty index set `S : Finset (Fin N)`, so repeated values of $y$ are counted by index. The page prints the numerator as "$(\sum_{y\in v} -a)$", omitting the summand; the formula stated here, $\sum_{y\in v} y - a$, is the one the same page uses two lines later.
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 5, Sect. 2

import Mathlib
import Definitions.Def_SimplexProj_Condat_IsSimplexProjection

namespace SimplexProj.Condat

/-- Condat, Sect. 2, p. 5: for every subsequence `v` of `y` (a nonempty set `S` of indices),
`ρ = (∑_{y ∈ v} y - a)/|v|` is a lower bound of the threshold `τ` of Proposition 2.2
(`x = P_Δ(y)`, `x_n = max {y_n - τ, 0}`). Standing assumptions of p. 1: `N ≥ 1`, `a > 0`. -/
theorem subsequence_mean_le_threshold (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a)
    (y x : Fin N → ℝ) (hx : IsSimplexProjection a y x)
    (τ : ℝ) (hτ : ∀ n, x n = max (y n - τ) 0)
    (S : Finset (Fin N)) (hS : S.Nonempty) :
    (∑ n ∈ S, y n - a) / S.card ≤ τ := by sorry

end SimplexProj.Condat
