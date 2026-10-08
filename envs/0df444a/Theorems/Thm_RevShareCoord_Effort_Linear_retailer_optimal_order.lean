-- Prove2me | Theorems.Thm_RevShareCoord_Effort_Linear_retailer_optimal_order
-- name    : RevShareCoord.Effort.Linear.retailer_optimal_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:05:48.500078+00:00
-- url     : https://prove2.me/theorems/03db99b7-5535-4d2d-9e82-78c5ba47ae7f
-- title:
--   Sec. 4.2.2, pp. 23–24 — the retailer's reduced profit, optimal order q(w, φ) and optimal profit (φ − w)²/(4(φ − φ²τ²))
-- statement:
--   In the linear example, let $0 \le \tau < 1$, $0 < \phi \le 1$ and $w \ge 0$. Then:
--
--   1. along the effort rule $e(q) = \phi\tau q$, for every $q$,
--   $$
--   \pi_r(q, e(q)) = q\,[\phi - q(\phi - \phi^2\tau^2) - w];
--   $$
--   2. the retailer has exactly one optimal response to $\{\phi, w\}$ over $q, e \ge 0$, namely $\big(q(w,\phi), e(q(w,\phi))\big)$ with
--   $$
--   q(w, \phi) = \frac{\phi - w}{2(\phi - \phi^2\tau^2)} \text{ if } w < \phi, \qquad q(w, \phi) = 0 \text{ otherwise};
--   $$
--   3. if $w < \phi$, then $q(w, \phi) > 0$ and the retailer's optimal profit is
--   $$
--   \pi_r(q(w,\phi)) = \frac{(\phi - w)^2}{4(\phi - \phi^2\tau^2)}.
--   $$
--
--   This determines the retailer's behaviour under every contract and therefore the supplier's profit as a function of $(w, \phi)$.
--
--   **Formalization Note.** The page optimizes effort first and quantity second; the statement asserts the joint optimum over the quadrant, which is what the retailer actually solves. The bound $\tau < 1$ (the page allows $\tau \in [0, 1]$) gives $\phi\tau^2 < 1$, which makes $\pi_r$ jointly strictly concave in $(q, e)$; this is the reading under which the page's remark that "the upper bound on $\tau$ ensures that the problem is jointly concave" holds.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 23 (PDF p. 24), Section 4.2.2, display of π_r(q, e(q)) and q(w, φ); p. 24 (PDF p. 25), 'assuming w < φ, otherwise q(w, φ) = 0' and π_r(q(w, φ))

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

namespace RevShareCoord.Effort.Linear

/-- Sec. 4.2.2, pp. 23–24: the retailer's profit along `e(q) = φτq` is
`q[φ − q(φ − φ²τ²) − w]`; the retailer's unique optimal response to `{φ, w}` is
`(q(w, φ), e(q(w, φ)))`, and when `w < φ` its profit there is `(φ − w)²/(4(φ − φ²τ²))`. -/
theorem retailer_optimal_order (τ φ w : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (hw : 0 ≤ w) :
    (∀ q : ℝ, retailerProfit τ φ w q (effort τ φ q) = q * (φ - q * (φ - φ ^ 2 * τ ^ 2) - w)) ∧
    (∀ x : ℝ × ℝ, IsRetailerResponse τ φ w x ↔
      x = (orderQty τ φ w, effort τ φ (orderQty τ φ w))) ∧
    (w < φ → 0 < orderQty τ φ w ∧
      retailerProfit τ φ w (orderQty τ φ w) (effort τ φ (orderQty τ φ w)) =
        (φ - w) ^ 2 / (4 * (φ - φ ^ 2 * τ ^ 2))) ∧
    (φ ≤ w → orderQty τ φ w = 0) := by sorry

end RevShareCoord.Effort.Linear
