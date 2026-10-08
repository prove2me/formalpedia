-- Prove2me | Theorems.Thm_SuReturns_Coordination_proposition5_sales_rebate
-- name    : SuReturns.Coordination.proposition5_sales_rebate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:35.651489+00:00
-- url     : https://prove2.me/theorems/114bae94-e7ca-4753-922f-6ab5e40662f1
-- title:
--   Proposition 5, p. 18 — the sales rebate u = (E max(V, s) − s)(w − c)/(c − s) coordinates the supply chain
-- statement:
--   Consider the supply chain of Section 5 (valuations $V\sim\nu$ with finite mean $\mu$, nonnegative demand $X\sim D$ with distribution function $F$, $0 \le s < c < \mu$) under a sales rebate contract: the retailer pays the wholesale price $w$, receives a rebate $u$ for every unit sold, whether or not it is later returned, and bears all unsold and returned units at salvage value $s$. Its profit is (25),
--   $$\Pi_R(p,q,r) = [(p-s+u)\bar G(r) + (p-r+u)G(r)]\,S(p,q,r) - (w-s)q.$$
--   Let $p^{SC} = E\max(V,s)$, $r^{SC} = s$ and $\bar F(q^{SC}) = (c-s)/(E\max(V,s)-s)$. If $w \ge s$ and
--   $$u = \frac{E\max(V,s)-s}{c-s}\cdot(w-c), \tag{26}$$
--   then the supply chain optimal triple is optimal for the retailer:
--   $$\Pi_R(p,q,r) \le \Pi_R(p^{SC},q^{SC},r^{SC}) \qquad \text{for all } p,\ r\in\mathbb R,\ q\ge 0.$$
--
--   The rebate coordinates without the manufacturer distinguishing new from returned units; it only needs to observe sales.
--
--   **Formalization Note** The hypothesis $w \ge s$ is added: for $w < s$ the retailer's profit at $(p^{SC}, r^{SC})$ is $\kappa\,[(E\max(V,s)-s)E\min(X,q) - (c-s)q]$ with $\kappa = (w-s)/(c-s) < 0$, which is unbounded above in $q$, so no optimum exists. The paper's own range is $w \ge c$ (p. 19), which implies it. That the triple maximizes total profit is Proposition 2 and is not restated. Demand is nonnegative and stocks are $q \ge 0$.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 18, Proposition 5, (26); proof p. 28

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.Coordination

theorem proposition5_sales_rebate (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < SuReturns.PartialRefunds.meanValuation ν)
    (qSC : ℝ) (hqSC : 1 - cdf D qSC = (c - s) / (SuReturns.PartialRefunds.reservationPrice ν s - s))
    (w u : ℝ) (hws : s ≤ w)
    (hu : u = (SuReturns.PartialRefunds.reservationPrice ν s - s) / (c - s) * (w - c)) :
    ∀ p r q : ℝ, 0 ≤ q →
      retailerRebate ν D s w u p q r ≤ retailerRebate ν D s w u (SuReturns.PartialRefunds.reservationPrice ν s) qSC s := by sorry

end SuReturns.Coordination
