-- Prove2me | Theorems.Thm_SennottDP_ResidualLife_moment_finite_iff_tail
-- name    : SennottDP.ResidualLife.moment_finite_iff_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T10:26:12.67287+00:00
-- url     : https://prove2.me/theorems/23a4b894-f13e-46f5-855e-34abbf7afa42
-- title:
--   Remark 9.2.2 — E[Y^k] < ∞ iff ∑ y^{k−1} F*(y) < ∞
-- statement:
--   Let $Y$ take values in $\{1,2,\dots\}$ with tail $F^*(y) = P(Y>y)$, and let $k \ge 2$. Then
--   $$E[Y^k] < \infty \iff \sum_{y} y^{k-1}F^*(y) < \infty.$$
--
--   This is the finiteness criterion used to show that a distribution has finite moments: it suffices to control the tail $F^*$.
--
--   **Formalization Note** The series runs over all $y \ge 0$; its $y = 0$ term vanishes because $k - 1 \ge 1$. The case $k = 1$ is the first identity of Proposition 9.2.1 and is not part of this statement, which, like the book, is read off (9.4) for $k \ge 2$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 203, Remark 9.2.2

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), Remark 9.2.2, p. 203: for `k ≥ 2`, `E[Y^k] < ∞` if and only if
`∑_y y^{k-1} F*(y) < ∞`. -/
theorem moment_finite_iff_tail (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (k : ℕ) (hk : 2 ≤ k) :
    moment u k < ∞ ↔ ∑' y : ℕ, (y : ℝ≥0∞) ^ (k - 1) * tail u y < ∞ := by sorry

end SennottDP.ResidualLife
