-- Prove2me | Theorems.Thm_SuReturns_Coordination_proposition4_direct_returns
-- name    : SuReturns.Coordination.proposition4_direct_returns
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:10.490018+00:00
-- url     : https://prove2.me/theorems/dcdf729a-5d00-4279-aa45-fc483f675f0c
-- title:
--   Proposition 4, p. 17 — with direct-to-manufacturer returns, the buy-back (22)–(23) makes the chain optimum a Nash equilibrium with retailer share φ
-- statement:
--   Consider the supply chain of Section 5 (valuations $V\sim\nu$ with finite mean $\mu$, nonnegative demand $X\sim D$ with distribution function $F$, $0 \le s < c < \mu$), in which consumers return the product directly to the manufacturer: the manufacturer chooses the refund $r$, the retailer chooses the price $p$ and stock $q$. Their profits are (19) and (21). Let
--   $$p^{SC} = E\max(V,s), \qquad \bar F(q^{SC}) = \frac{c-s}{E\max(V,s)-s}, \qquad r^{SC} = s,$$
--   let $\phi \in [0,1]$, $\bar\phi = 1-\phi$, and let the buy-back contract be
--   $$w = \phi c + \bar\phi\,E\max(V,s), \qquad b = \phi s + \bar\phi\,E\max(V,s). \tag{22–23}$$
--   Then the retailer choosing $(p^{SC},q^{SC})$ and the manufacturer choosing $r^{SC}$ is a Nash equilibrium that gives the retailer the fraction $\phi$ of the supply chain profit:
--   1. given $r = s$, $\Pi_R(p,q,s) \le \Pi_R(p^{SC},q^{SC},s)$ for all $p$ and $q \ge 0$;
--   2. given $(p^{SC},q^{SC})$, $\Pi_M(p^{SC},q^{SC},r) \le \Pi_M(p^{SC},q^{SC},s)$ for all $r$;
--   3. $\Pi_R(p^{SC},q^{SC},s) = \phi\,\Pi_T(p^{SC},q^{SC},s)$.
--
--   The manufacturer's control of the refund removes the retailer's incentive to distort it, so a two-parameter buy-back suffices here.
--
--   **Formalization Note** The Nash equilibrium is written out as the two best-response conditions, each player optimizing while the other's choice is held fixed; in (2) the retailer's price stays at $p^{SC}$, and a deviation of the manufacturer acts on sales only through the demand rule (6). That $(p^{SC},q^{SC},s)$ maximizes total profit is Proposition 2 and is not restated. Demand is nonnegative and stocks are $q \ge 0$.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), pp. 17–18, Proposition 4, (22)–(23); proof p. 28

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.Coordination

theorem proposition4_direct_returns (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < SuReturns.PartialRefunds.meanValuation ν)
    (qSC : ℝ) (hqSC : 1 - cdf D qSC = (c - s) / (SuReturns.PartialRefunds.reservationPrice ν s - s))
    (φ w b : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hw : w = φ * c + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s)
    (hb : b = φ * s + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s) :
    (∀ p q : ℝ, 0 ≤ q →
        retailerDirect ν D w b p q s ≤ retailerDirect ν D w b (SuReturns.PartialRefunds.reservationPrice ν s) qSC s) ∧
      (∀ r : ℝ, manufacturerDirect ν D c s w b (SuReturns.PartialRefunds.reservationPrice ν s) qSC r ≤
        manufacturerDirect ν D c s w b (SuReturns.PartialRefunds.reservationPrice ν s) qSC s) ∧
      retailerDirect ν D w b (SuReturns.PartialRefunds.reservationPrice ν s) qSC s =
        φ * chainProfit ν D c s (SuReturns.PartialRefunds.reservationPrice ν s) qSC s := by sorry

end SuReturns.Coordination
