-- Prove2me | Theorems.Thm_RLPBidPrice_Directional_superdiff_eq_dualOpt
-- name    : RLPBidPrice.Directional.superdiff_eq_dualOpt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T13:12:21.131507+00:00
-- url     : https://prove2.me/theorems/61e7e72d-0e3a-4b48-b41b-d5a49ed8e002
-- title:
--   Proof of Proposition 2, p. 212 (corrected: the dual optimal set of (14)) — ∂v(x, Y) = {optimal dual prices}, uniformly bounded by r̄
-- statement:
--   Let $A$ be a 0/1 incidence matrix with nonzero columns, $r \ge 0$, $x$ a capacity vector with every component $x^i > 0$, and $Y \ge 0$ a demand vector. Then the superdifferential of the concave function $z \mapsto v(z, Y)$ at $x$,
--   $$\partial v(x, Y) = \{\mu \in \mathbb{R}^m : v(z, Y) \le v(x, Y) + \mu^\top (z - x) \text{ for all } z \ge 0\},$$
--   is exactly the set of optimal vectors of dual prices,
--   $$\partial v(x, Y) = \Big\{\mu \ge 0 : L(x, \mu) = \min_{\mu' \ge 0} L(x, \mu')\Big\}, \qquad L(x, \mu) = \sum_{j=1}^n Y^j (r^j - \mu^\top A^j)^+ + \mu^\top x,$$
--   and every $\mu \in \partial v(x, Y)$ satisfies $0 \le \mu^i \le \bar r = \max_j r^j$ for every leg $i$. In particular $\partial v(x, Y)$ is bounded uniformly in $Y$.
--
--   **Formalization Note.** The superdifferential is taken over the feasible capacities $z \ge 0$. $\bar r$ is written `⨆ j, r j`. $x > 0$ is the paper's implicit setting for differentiating at a capacity vector (at a zero capacity the dual prices of that leg are unbounded). The time index $k$ is dropped.
--
--   **Correction.** The paper states $\partial v_k(x, Y) = \{\mu : \mu^\top x = v_k(x, Y),\ \mu^\top A \le r,\ \mu \ge 0\}$, which omits the dual variables of the constraints $y \le Y$. With one leg, one itinerary, $r = 1$, $x = 1$ and $Y = 1/2$, the printed set is $\{1/2\}$ while $v(z, Y) = \min(z, 1/2)$ has superdifferential $\{0\}$ at $x = 1$.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 212, proof of Proposition 2, first two sentences

import Mathlib
import Definitions.Def_RLPBidPrice_Directional_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Directional

/-- Proof of Proposition 2, p. 212 (corrected): for `x > 0` the superdifferential of
`z ↦ v(z, y₀)` at `x` is the set of optimal dual price vectors of (14), and it lies in the box
`0 ≤ μ ≤ r̄`, `r̄ = max_j r^j`, whatever `y₀` is. -/
theorem superdiff_eq_dualOpt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : ∀ i, 0 < x i)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) :
    superdiff A r x y₀ = {μ | IsDualOpt A r x y₀ μ} ∧
      ∀ μ ∈ superdiff A r x y₀, ∀ i, 0 ≤ μ i ∧ μ i ≤ ⨆ j, r j := by sorry

end RLPBidPrice.Directional
