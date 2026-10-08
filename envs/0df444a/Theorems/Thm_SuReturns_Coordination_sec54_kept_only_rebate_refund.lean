-- Prove2me | Theorems.Thm_SuReturns_Coordination_sec54_kept_only_rebate_refund
-- name    : SuReturns.Coordination.sec54_kept_only_rebate_refund
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:04.58099+00:00
-- url     : https://prove2.me/theorems/95bb05d9-af7c-4f0c-812b-d76a86ebb54d
-- title:
--   Sec. 5.4, p. 19 — with a rebate on kept units only, the retailer's optimal refund is r* = s − u < s
-- statement:
--   Suppose the manufacturer pays the sales rebate $u > 0$ only for units that are sold and kept by the consumer. The retailer's profit is then
--   $$\Pi_R(p,q,r) = [(p-s+u)\bar G(r) + (p-r)G(r)]\,S(p,q,r) - (w-s)q,$$
--   with $S$ the expected sales under the demand rule (6), valuations of finite mean and nonnegative demand. For every stock $q \ge 0$, the refund $r^* = s-u$ with the price $E\max(V,s-u)$ is optimal for the retailer, and it lies below the supply chain optimal refund $s$:
--   $$\Pi_R(p,q,r) \le \Pi_R\big(E\max(V,s-u),\,q,\,s-u\big)\quad\text{for all } p,\ r\in\mathbb R,\ q\ge 0, \qquad s-u < s.$$
--
--   So a rebate that excludes returned units distorts the refund downward, which is why the coordinating rebate of Proposition 5 must be paid on all sold units.
--
--   **Formalization Note** The paper gives this contract in prose only; the profit is (24) with the rebate removed from the returned-units term. Only optimality of $r^* = s-u$ (with the matching price) at each fixed $q$ is stated, not uniqueness.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 19, Sec. 5.4, final remark on sales rebates

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.Coordination

theorem sec54_kept_only_rebate_refund (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (s w u : ℝ) (hu : 0 < u) :
    (∀ p r q : ℝ, 0 ≤ q →
        retailerKeptRebate ν D s w u p q r ≤
          retailerKeptRebate ν D s w u (SuReturns.PartialRefunds.reservationPrice ν (s - u)) q (s - u)) ∧
      s - u < s := by sorry

end SuReturns.Coordination
