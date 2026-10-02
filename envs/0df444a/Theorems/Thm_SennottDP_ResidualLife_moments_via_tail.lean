-- Prove2me | Theorems.Thm_SennottDP_ResidualLife_moments_via_tail
-- name    : SennottDP.ResidualLife.moments_via_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T10:20:15.831208+00:00
-- url     : https://prove2.me/theorems/7fb1c9a0-38ed-4d43-af92-d0978cb5a504
-- title:
--   Proposition 9.2.1 — moments of Y in terms of the tail F*
-- statement:
--   Let $Y$ take values in $\{1,2,\dots\}$ with distribution $u_y = P(Y=y)$ and tail $F^*(y) = P(Y>y)$, $y \ge 0$. Then
--   $$E[Y] = \sum_{y=0}^{\infty} F^*(y)$$
--   and, for every $k \ge 2$,
--   $$E[Y^k] = 1 + \sum_{z=0}^{k-1}\binom{k}{z}\left[\sum_{y=1}^{\infty} y^z F^*(y)\right].$$
--   All quantities lie in $[0,\infty]$, so both identities hold whether or not the moments are finite.
--
--   These identities express every moment of $Y$ through the tail of its distribution; they are the basis for all finiteness criteria of Section 9.2.
--
--   **Formalization Note** Moments and the tail sums are `ℝ≥0∞`-valued series. The inner sum starts at $y = 1$ (written with an `if 1 ≤ y` guard, which matters for $z = 0$ since Lean has $0^0 = 1$), while the formula for $E[Y]$ sums from $y = 0$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 202, Proposition 9.2.1, Eq. (9.4)

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), Proposition 9.2.1, p. 202: for `Y` on `{1, 2, …}` with tail `F*`,
`E[Y] = ∑_{y=0}^∞ F*(y)` and, for `k ≥ 2`,
`E[Y^k] = 1 + ∑_{z=0}^{k-1} C(k,z) [∑_{y=1}^∞ y^z F*(y)]` (9.4). -/
theorem moments_via_tail (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) :
    moment u 1 = ∑' y, tail u y ∧
    ∀ k : ℕ, 2 ≤ k →
      moment u k = 1 + ∑ z ∈ Finset.range k,
        (Nat.choose k z : ℝ≥0∞) * ∑' y : ℕ, (if 1 ≤ y then (y : ℝ≥0∞) ^ z * tail u y else 0) := by sorry

end SennottDP.ResidualLife
