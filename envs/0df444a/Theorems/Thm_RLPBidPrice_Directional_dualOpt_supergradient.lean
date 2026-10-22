-- Prove2me | Theorems.Thm_RLPBidPrice_Directional_dualOpt_supergradient
-- name    : RLPBidPrice.Directional.dualOpt_supergradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T13:11:56.357698+00:00
-- url     : https://prove2.me/theorems/93b893ba-7051-4d0b-8aa2-5163263413d4
-- title:
--   §3.1, p. 212 (corrected: ≤ for ≥) — an optimal dual price vector μ(x, Y) is a supergradient: v(z, Y) ≤ v(x, Y) + μᵀ(z − x) for all z ≥ 0
-- statement:
--   Let $A$ be a 0/1 incidence matrix with nonzero columns, $r \ge 0$, $x \ge 0$ a capacity vector and $Y \ge 0$ a demand vector. Let $\mu$ be an optimal vector of dual prices for the capacity constraints, i.e. $\mu \ge 0$ minimizes $L(x, \mu) = \sum_j Y^j (r^j - \mu^\top A^j)^+ + \mu^\top x$ over $\mu \ge 0$. Then for every capacity vector $z \ge 0$,
--   $$v(z, Y) \le v(x, Y) + \mu^\top (z - x),$$
--   where $v(x, Y) = \max\{r^\top y : Ay \le x,\ 0 \le y \le Y\}$.
--
--   In words: for every realization of demand, the dual price vector is a supergradient of the concave function $z \mapsto v(z, Y)$ (the paper says "subgradient").
--
--   **Formalization Note.** $z$ ranges over the feasible capacities $z \ge 0$ (for other $z$ the LP has no value). The time index $k$ is dropped.
--
--   **Correction.** The paper prints the inequality as $v_k(z, Y) \ge v_k(x, Y) + \mu^\top(x, Y)(z - x)$. Since $v(\cdot, Y)$ is concave the inequality goes the other way: with one leg, one itinerary, $r = 1$, $Y = 5$, $x = 1$ (so $\mu = 1$) and $z = 10$, the printed inequality reads $5 \ge 10$.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 212, §3.1, first display

import Mathlib
import Definitions.Def_RLPBidPrice_Directional_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Directional

/-- §3.1, p. 212 (sign corrected): an optimal dual price vector `μ` of (14) at `x` is a
supergradient of the concave map `z ↦ v(z, y₀)` on the capacities `z ≥ 0`. -/
theorem dualOpt_supergradient {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) (μ : Fin m → ℝ) (hμ : IsDualOpt A r x y₀ μ)
    (z : Fin m → ℝ) (hz : 0 ≤ z) :
    piValue A r z y₀ ≤ piValue A r x y₀ + μ ⬝ᵥ (z - x) := by sorry

end RLPBidPrice.Directional
