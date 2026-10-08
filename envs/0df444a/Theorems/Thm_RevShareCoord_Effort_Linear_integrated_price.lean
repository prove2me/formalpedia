-- Prove2me | Theorems.Thm_RevShareCoord_Effort_Linear_integrated_price
-- name    : RevShareCoord.Effort.Linear.integrated_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:05:57.793082+00:00
-- url     : https://prove2.me/theorems/4beadebd-978e-467b-b7ca-4e41925cca11
-- title:
--   Sec. 4.2.2, p. 24 — the integrated retail price p_I = (1 + c(1 − 2τ²))/(2(1 − τ²)) and its monotonicity in c
-- statement:
--   In the linear example, let $0 \le \tau < 1$. For every unit cost $0 < c < 1$, the integrated channel's profit $\Pi(q, e) = R(q, e) - e^2 - qc$ has exactly one maximizer over $q, e \ge 0$, and it is the retailer's solution under marginal-cost pricing, $\big(q(c, 1), e(q(c, 1))\big)$ with $w = c$, $\phi = 1$. The retail price charged there is
--
--   $$
--   p_I = \frac{1 + c(1 - 2\tau^2)}{2(1 - \tau^2)} .
--   $$
--
--   As a function of $c \in (0, 1)$, $p_I$ is strictly increasing if $\tau < 1/\sqrt 2$, constant (equal to $1$) if $\tau = 1/\sqrt 2$, and strictly decreasing if $\tau > 1/\sqrt 2$.
--
--   When effort matters enough, a higher production cost lowers the integrated channel's price: the reduction in effort shrinks the market by more than the quantity effect raises the price.
--
--   **Formalization Note.** $\tau = 1$ is excluded: at $\tau = 1$ the integrated profit along $e = \tau q$ is $q(1-c)$, unbounded in $q$, and $p_I$ divides by zero. $c < 1$ makes the integrated quantity positive. The page states only the strict cases; the constant case at $\tau = 1/\sqrt 2$ is added to complete the trichotomy.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 24 (PDF p. 25), Section 4.2.2, 'The integrated channel solution is obtained from the retailer's solution with marginal cost pricing … decreasing in c if τ > 1/√2.'

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

namespace RevShareCoord.Effort.Linear

/-- Sec. 4.2.2, p. 24: the integrated channel's unique optimum is the retailer's solution with
`w = c`, `φ = 1`; its retail price is `p_I = (1 + c(1 − 2τ²))/(2(1 − τ²))`, which is increasing in
`c` if `τ < 1/√2`, decreasing if `τ > 1/√2` (and constant if `τ = 1/√2`). -/
theorem integrated_price (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    (∀ c : ℝ, 0 < c → c < 1 → ∀ x : ℝ × ℝ,
      (x ∈ quadrant ∧ IsMaxOn (fun y : ℝ × ℝ => channelProfit τ c y.1 y.2) quadrant x) ↔
        x = (orderQty τ 1 c, effort τ 1 (orderQty τ 1 c))) ∧
    (∀ c : ℝ, 0 < c → c < 1 →
      integratedPrice τ c = (1 + c * (1 - 2 * τ ^ 2)) / (2 * (1 - τ ^ 2))) ∧
    (τ < 1 / Real.sqrt 2 → StrictMonoOn (integratedPrice τ) (Set.Ioo 0 1)) ∧
    (τ = 1 / Real.sqrt 2 → ∀ c ∈ Set.Ioo (0 : ℝ) 1, integratedPrice τ c = 1) ∧
    (1 / Real.sqrt 2 < τ → StrictAntiOn (integratedPrice τ) (Set.Ioo 0 1)) := by sorry

end RevShareCoord.Effort.Linear
