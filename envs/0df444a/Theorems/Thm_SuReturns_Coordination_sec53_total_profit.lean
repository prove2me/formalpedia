-- Prove2me | Theorems.Thm_SuReturns_Coordination_sec53_total_profit
-- name    : SuReturns.Coordination.sec53_total_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:01.204981+00:00
-- url     : https://prove2.me/theorems/7e814a0a-3d47-4e8b-832b-b70f22317999
-- title:
--   Sec. 5.3, p. 17 — with direct-to-manufacturer returns, Π_R (19) + Π_M (21) is the total profit (15)
-- statement:
--   With direct-to-manufacturer returns under a buy-back $(w,b)$, the retailer's profit is (19) and the manufacturer's is (21):
--   $$\Pi_R(p,q,r) = (p-b)\,S - (w-b)q, \qquad \Pi_M(p,q,r) = [(b-s)\bar G(r) + (b-r)G(r)]\,S - [(c-s)-(w-b)]q,$$
--   where $S = S(p,q,r)$ is expected sales under the demand rule (6) and $\bar G(r) + G(r) = 1$. For every $p$, $q$, $r$ their sum is the total supply chain profit (15):
--   $$\Pi_R(p,q,r) + \Pi_M(p,q,r) = \Pi_T(p,q,r) = [(p-s)\bar G(r) + (p-r)G(r)]\,S - (c-s)q.$$
--
--   This identity is what lets the allocation in Proposition 4 be read as a split of the total supply chain profit.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 17, Sec. 5.3, after (21)

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.Coordination

theorem sec53_total_profit (ν D : Measure ℝ) [IsProbabilityMeasure ν] (c s w b : ℝ) :
    ∀ p q r : ℝ, retailerDirect ν D w b p q r + manufacturerDirect ν D c s w b p q r =
      chainProfit ν D c s p q r := by sorry

end SuReturns.Coordination
