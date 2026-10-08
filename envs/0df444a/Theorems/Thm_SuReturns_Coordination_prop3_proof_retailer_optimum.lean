-- Prove2me | Theorems.Thm_SuReturns_Coordination_prop3_proof_retailer_optimum
-- name    : SuReturns.Coordination.prop3_proof_retailer_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:10.506628+00:00
-- url     : https://prove2.me/theorems/666a4b3b-6072-4ecf-b986-171073fdb771
-- title:
--   Proof of Proposition 3, p. 27 — under (31) the retailer optimum is p* = E max(V, b − l), F̄(q*) = (w − b)/(E max(V, b − l) − b), r* = b − l
-- statement:
--   Consider a retailer under a differentiated buy-back contract $(w,b,l)$: wholesale price $w$, credit $b$ for each unsold unit and $b-l$ for each returned unit. Valuations have law $\nu$ with finite mean and market demand $X \sim D$ is nonnegative. The retailer's profit is (31),
--   $$\Pi_R(p,q,r) = [(p-b)\bar G(r) + (p-r-l)G(r)]\,S(p,q,r) - (w-b)q,$$
--   with $S$ the expected sales under the demand rule (6). Suppose $E\max(V,b-l) - b > 0$ and let $q^*$ satisfy
--   $$\bar F(q^*) = 1 - F(q^*) = \frac{w-b}{E\max(V,b-l)-b},$$
--   where $F$ is the distribution function of $D$. Then $p^* = E\max(V,b-l)$, $q^*$ and $r^* = b-l$ are optimal for the retailer:
--   $$\Pi_R(p,q,r) \le \Pi_R\big(E\max(V,b-l),\,q^*,\,b-l\big) \qquad \text{for all } p,\ r \in \mathbb R,\ q \ge 0.$$
--
--   This is the retailer's best response to an arbitrary differentiated buy-back; Proposition 3 then chooses $(w,b,l)$ so that it coincides with the supply chain optimum.
--
--   **Formalization Note** The positivity of $E\max(V,b-l)-b$ is the condition under which the paper's fractile $\bar F^{-1}\big((w-b)/(E\max(V,b-l)-b)\big)$ is defined; without it the fraction is Lean's junk value $x/0 = 0$. The optimal quantity is stated as any $q^*$ satisfying the fractile equation (the paper writes $\bar F^{-1}$); no continuity of $D$ is assumed. Demand is nonnegative and competing stocks satisfy $q \ge 0$. Optimality, not uniqueness, is claimed.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 27, proof of Proposition 3, after (31)

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.Coordination

theorem prop3_proof_retailer_optimum (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (w b l qstar : ℝ) (hpos : 0 < SuReturns.PartialRefunds.reservationPrice ν (b - l) - b)
    (hq : 1 - cdf D qstar = (w - b) / (SuReturns.PartialRefunds.reservationPrice ν (b - l) - b)) :
    ∀ p r q : ℝ, 0 ≤ q →
      retailerDiffBuyback ν D w b l p q r ≤
        retailerDiffBuyback ν D w b l (SuReturns.PartialRefunds.reservationPrice ν (b - l)) qstar (b - l) := by sorry

end SuReturns.Coordination
