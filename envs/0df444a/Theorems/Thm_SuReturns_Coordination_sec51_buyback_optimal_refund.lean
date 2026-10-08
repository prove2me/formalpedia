-- Prove2me | Theorems.Thm_SuReturns_Coordination_sec51_buyback_optimal_refund
-- name    : SuReturns.Coordination.sec51_buyback_optimal_refund
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:55.32514+00:00
-- url     : https://prove2.me/theorems/2216bf95-2ba5-4bc4-8ec4-26b9192682c3
-- title:
--   Sec. 5.1, p. 15 — under a standard buy-back the retailer's optimal refund is r* = b
-- statement:
--   Consider a retailer under a standard buy-back contract with wholesale price $w$ and buy-back price $b$, facing consumers with valuation law $\nu$ (finite mean) and nonnegative market demand $X \sim D$. Its profit is (14),
--   $$\Pi_R(p,q,r) = [(p-b)\bar G(r) + (p-r)G(r)]\,S(p,q,r) - (w-b)q,$$
--   where $S(p,q,r)$ is expected sales under the demand rule (6) (consumers buy iff $p \le E\max(V,r)$). Then for every stock $q \ge 0$, the refund $r^* = b$ together with the price $E\max(V,b)$ is optimal:
--   $$\Pi_R(p,q,r) \le \Pi_R\big(E\max(V,b),\,q,\,b\big) \qquad \text{for all } p,\ r \in \mathbb R,\ q \ge 0.$$
--
--   This is the observation that a standard buy-back distorts the retailer's returns policy: the supply chain's optimal refund is the salvage value $s$, but the retailer's is the buy-back price $b$, which differs from $s$ whenever the buy-back is used for coordination ($b > s$).
--
--   **Formalization Note** The statement holds for every $w$ and $b$, and for each fixed $q$; only the optimality of $r^* = b$ (with the matching price) is stated, not its uniqueness and not the paper's further remark that buy-backs fail to coordinate unless $b = s$. Demand is assumed nonnegative ($D((-\infty,0)) = 0$) and stocks $q \ge 0$, as the paper's quantities are; without them the profit is unbounded.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 15, Sec. 5.1 (after (14)–(15))

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.Coordination

theorem sec51_buyback_optimal_refund (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (w b : ℝ) :
    ∀ p r q : ℝ, 0 ≤ q →
      retailerBuyback ν D w b p q r ≤ retailerBuyback ν D w b (SuReturns.PartialRefunds.reservationPrice ν b) q b := by sorry

end SuReturns.Coordination
