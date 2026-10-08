-- Prove2me | Theorems.Thm_RevShareCoord_Effort_Linear_retailer_optimal_effort
-- name    : RevShareCoord.Effort.Linear.retailer_optimal_effort
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:05:33.342823+00:00
-- url     : https://prove2.me/theorems/61b847b4-7319-40c2-94ea-cf79f8426089
-- title:
--   Sec. 4.2.2, p. 23 — the retailer's unique optimal effort is e(q) = φτq
-- statement:
--   In the linear example $P(q, e) = 1 - q + 2\tau e$, $R(q, e) = qP(q, e)$, $g(e) = e^2$, let $0 \le \tau < 1$, $0 < \phi \le 1$, let $w$ be any wholesale price and $q \ge 0$ a fixed quantity. Then the effort level
--
--   $$
--   e(q) = \phi\tau q
--   $$
--
--   is nonnegative and is the unique maximizer of $e \mapsto \pi_r(q, e) = \phi R(q, e) - e^2 - qw$ over $e \ge 0$. Moreover $e(q)$ is increasing in the retailer's share $\phi \ge 0$.
--
--   This is the first step of the retailer's problem in the example; the retailer's reduced problem in $q$ is obtained by substituting $e(q)$.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 23 (PDF p. 24), Section 4.2.2, 'Let e(q) be the retailer's unique optimal effort, e(q) = φτq.'

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

namespace RevShareCoord.Effort.Linear

/-- Sec. 4.2.2, p. 23: for a fixed quantity `q ≥ 0`, the retailer's unique optimal effort is
`e(q) = φτq`, which is increasing in `φ`. -/
theorem retailer_optimal_effort (τ φ w q : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (hq : 0 ≤ q) :
    0 ≤ effort τ φ q ∧
    IsMaxOn (fun e => retailerProfit τ φ w q e) (Set.Ici 0) (effort τ φ q) ∧
    (∀ e : ℝ, 0 ≤ e → IsMaxOn (fun e' => retailerProfit τ φ w q e') (Set.Ici 0) e →
      e = effort τ φ q) ∧
    MonotoneOn (fun φ' => effort τ φ' q) (Set.Ici 0) := by sorry

end RevShareCoord.Effort.Linear
