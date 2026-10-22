-- Prove2me | Theorems.Thm_RLPBidPrice_Directional_piValue_lipschitz
-- name    : RLPBidPrice.Directional.piValue_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T13:11:43.952112+00:00
-- url     : https://prove2.me/theorems/b0104d1a-c45c-4fe2-817a-7873d16187fa
-- title:
--   Lemma 2 — |v(x + h eⁱ, Y) − v(x, Y)| ≤ h r̄ with r̄ = max_j r^j
-- statement:
--   Let $A$ be a 0/1 leg–itinerary incidence matrix with nonzero columns, $r \ge 0$ the fares, $x \ge 0$ a capacity vector and $Y \ge 0$ a demand vector, and let $v(x, Y) = \max\{r^\top y : Ay \le x,\ 0 \le y \le Y\}$. For every leg $i$ and every $h \ge 0$,
--   $$|v(x + h e^i, Y) - v(x, Y)| \le h\, \bar r, \qquad \bar r = \max_{j} r^j,$$
--   where $e^i$ is the $i$-th unit vector.
--
--   This is the paper's Lipschitz bound (Lemma 2: "$v_k(x, Y)$ satisfies the Lipschitz condition in Lemma 1"): a constant $\bar r$ in each coordinate direction, uniform in $Y$. In the nondifferentiable case it is what makes the difference quotients of $v$ uniformly bounded.
--
--   **Formalization Note.** $\bar r$ is written $\sup_j r^j$ (`⨆ j, r j`), which is $\max_j r^j$ for $n \ge 1$ and $0$ when there are no itineraries. The paper's "for all $x$" is restricted to $x \ge 0$: for capacities with a negative entry the LP is infeasible and has no value. Fares $r \ge 0$ are an implicit hypothesis (revenues): if every $r^j < 0$ then $v \equiv 0$ and the bound $h \bar r < 0$ fails. The time index $k$ is dropped.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 210, Lemma 2 and the sentence preceding it

import Mathlib
import Definitions.Def_RLPBidPrice_Directional_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Directional

/-- Lemma 2 (p. 210) and the bound preceding it: raising the capacity of one leg by `h ≥ 0`
changes the perfect-information LP value by at most `h · r̄`, `r̄ = max_j r^j`. -/
theorem piValue_lipschitz {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) (i : Fin m) (h : ℝ) (hh : 0 ≤ h) :
    |piValue A r (x + h • Pi.single i 1) y₀ - piValue A r x y₀| ≤ h * ⨆ j, r j := by sorry

end RLPBidPrice.Directional
