-- Prove2me | Theorems.Thm_SuReturns_Coordination_proposition3_differentiated_buyback
-- name    : SuReturns.Coordination.proposition3_differentiated_buyback
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:16.328392+00:00
-- url     : https://prove2.me/theorems/b591d7fe-24aa-4fa8-bd38-89b147a1ed77
-- title:
--   Proposition 3, p. 16 — the differentiated buy-back (16)–(18) coordinates the supply chain and gives the retailer a share φ
-- statement:
--   Consider the supply chain of Section 5: valuations $V \sim \nu$ with finite mean $\mu$, nonnegative market demand $X \sim D$ with distribution function $F$, production cost $c$ and salvage value $s$ with $0 \le s < c < \mu$. By Proposition 2 the supply chain optimal decisions are
--   $$p^{SC} = E\max(V,s), \qquad \bar F(q^{SC}) = \frac{c-s}{E\max(V,s)-s}, \qquad r^{SC} = s.$$
--   Let $\phi \in [0,1]$, $\bar\phi = 1-\phi$, and let the differentiated buy-back contract have parameters
--   $$w = \phi c + \bar\phi\,E\max(V,s), \qquad b = \phi s + \bar\phi\,E\max(V,s), \qquad b - l = s. \tag{16–18}$$
--   Then, with $\Pi_R$ the retailer's profit (31) and $\Pi_T$ the total supply chain profit (15), both under the demand rule (6):
--   1. the supply chain optimal triple is optimal for the retailer:
--   $$\Pi_R(p,q,r) \le \Pi_R(p^{SC}, q^{SC}, r^{SC}) \qquad \text{for all } p,\ r\in\mathbb R,\ q \ge 0;$$
--   2. the retailer receives the fraction $\phi$ of the supply chain profit: $\Pi_R(p^{SC}, q^{SC}, r^{SC}) = \phi\,\Pi_T(p^{SC}, q^{SC}, r^{SC})$;
--   3. the contract can be implemented: $w \ge b$, $l \ge 0$ and $b - l \ge s$.
--
--   Thus distinguishing unsold from returned units, and crediting returned units exactly the salvage value, restores coordination of price, quantity and refund that a standard buy-back loses, while $\phi$ splits the optimal profit arbitrarily.
--
--   **Formalization Note** "Induces the retailer to maximize supply chain profit" is stated as: Proposition 2's chain-optimal triple is a retailer optimum. That the triple maximizes $\Pi_T$ is Proposition 2 itself (mission 1 of this series) and is not restated. Uniqueness is not claimed, and the stronger "every retailer optimum is chain optimal" is not claimed (it fails at $\phi = 0$, where the retailer earns zero on many choices). The demand law is nonnegative ($D((-\infty,0)) = 0$) and stocks are $q \ge 0$, as the paper's quantities are; the valuation law is a general probability measure with finite mean rather than a density. $q^{SC}$ is any solution of the fractile equation.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 16, Proposition 3, (16)–(18); proof p. 27

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.Coordination

theorem proposition3_differentiated_buyback (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < SuReturns.PartialRefunds.meanValuation ν)
    (qSC : ℝ) (hqSC : 1 - cdf D qSC = (c - s) / (SuReturns.PartialRefunds.reservationPrice ν s - s))
    (φ w b l : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hw : w = φ * c + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s)
    (hb : b = φ * s + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s)
    (hl : b - l = s) :
    (∀ p r q : ℝ, 0 ≤ q →
        retailerDiffBuyback ν D w b l p q r ≤
          retailerDiffBuyback ν D w b l (SuReturns.PartialRefunds.reservationPrice ν s) qSC s) ∧
      retailerDiffBuyback ν D w b l (SuReturns.PartialRefunds.reservationPrice ν s) qSC s =
        φ * chainProfit ν D c s (SuReturns.PartialRefunds.reservationPrice ν s) qSC s ∧
      b ≤ w ∧ 0 ≤ l ∧ s ≤ b - l := by sorry

end SuReturns.Coordination
