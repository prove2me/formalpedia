-- Prove2me | Theorems.Thm_RLPBidPrice_Directional_directional_derivative_eq_expected_u
-- name    : RLPBidPrice.Directional.directional_derivative_eq_expected_u
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T13:12:48.865776+00:00
-- url     : https://prove2.me/theorems/fdc5856e-615f-4787-bb74-cdebf4c29c11
-- title:
--   Proposition 2 (corrected: Eq. (22) includes the duals of y ≤ Y) — D(x; d) = E u(x, Y; d)
-- statement:
--   Let $A$ be a 0/1 leg–itinerary incidence matrix with nonzero columns, $r \ge 0$ the fares, and $x$ a capacity vector with every component $x^i > 0$. Let $Y$ be a measurable random demand vector on a probability space $(\Omega, P)$ with $Y \ge 0$ almost surely, and let $J^{PI}(x) = \mathbb{E}\, v(x, Y)$, where $v(x, Y) = \max\{r^\top y : Ay \le x,\ 0 \le y \le Y\}$. For every direction $d \in \mathbb{R}^m$ the one-sided directional derivative of $J^{PI}$ at $x$ exists and
--   $$D(x; d) = \lim_{h \downarrow 0} \frac{1}{h}\big[J^{PI}(x + hd) - J^{PI}(x)\big] = \mathbb{E}\, u(x, Y; d),$$
--   where
--   $$u(x, Y; d) = \min\{d^\top \mu : \mu \ge 0,\ L(x, \mu) = \min_{\mu' \ge 0} L(x, \mu')\}, \qquad L(x, \mu) = \sum_{j=1}^n Y^j (r^j - \mu^\top A^j)^+ + \mu^\top x,$$
--   is the least value of $d^\top\mu$ over the optimal vectors of dual prices of the capacity constraints.
--
--   No condition on the demand distribution is assumed: the result covers the nondifferentiable case, where the dual prices are not unique with positive probability and the averaged dual prices only estimate a supergradient. Averaging $u(x, Y_i; d)$ over simulated demands gives an unbiased estimator of the directional derivative.
--
--   **Formalization Note.** The limit is one-sided, $h \to 0^+$ (`nhdsWithin 0 (Set.Ioi 0)`); the paper's Eq. (12) writes $\lim_{h \to 0}$, whose two-sided version fails in the nondifferentiable case. $x > 0$ is implicit in the paper (it differentiates at a capacity vector; at a zero capacity a direction leaving $\{x \ge 0\}$ makes the LP infeasible). $u$ is a real `sInf`; for $x > 0$ and $Y \ge 0$ the optimal dual price set is nonempty and bounded, so $u$ is an attained minimum and bounded uniformly in $Y$. No integrability of $Y$ is needed: $v(x, Y)$ is bounded by $\sum_j r^j \max_i x^i$ because every itinerary uses a leg. The time index $k$ is dropped.
--
--   **Correction.** The paper defines $u$ by Eq. (22), $\min d^\top\mu$ subject to $\mu^\top x = v_k(x, Y)$, $\mu^\top A \le r$, $\mu \ge 0$, which omits the dual variables of $y \le Y$; with that $u$ the proposition is false (one leg, one itinerary, $r = 1$, $x = 1$, $Y$ uniform on $[0, 2]$, $d = 1$: $D(x; d) = P(Y > 1) = 1/2$ but the printed (22) gives $\mathbb{E}\min(Y, 1) = 3/4$). Here $u$ is taken over the optimal dual prices of the Lagrangian problem (14).
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 212, Proposition 2 (with Eq. (12), p. 210, and Eq. (22), p. 212)

import Mathlib
import Definitions.Def_RLPBidPrice_Directional_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Directional

/-- Proposition 2, p. 212, with Eq. (22) corrected: at a capacity vector `x > 0` the one-sided
directional derivative `D(x; d)` of `J^PI` exists for every direction `d` and equals
`E u(x, Y; d)`. -/
theorem directional_derivative_eq_expected_u {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (hA : IsIncidence A) (hr : 0 ≤ r)
    (x : Fin m → ℝ) (hx : ∀ i, 0 < x i)
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (d : Fin m → ℝ) :
    Filter.Tendsto (fun h : ℝ => h⁻¹ * (JPI P A r Y (x + h • d) - JPI P A r Y x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ ω, u A r x (Y ω) d ∂P)) := by sorry

end RLPBidPrice.Directional
