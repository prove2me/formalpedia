-- Prove2me | Theorems.Thm_SuReturns_PartialRefunds_corollary2_welfare
-- name    : SuReturns.PartialRefunds.corollary2_welfare
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:20.648907+00:00
-- url     : https://prove2.me/theorems/a047156c-8cee-456c-8d4b-97d1104481e6
-- title:
--   Corollary 2, p. 13 — the seller's optimal (p*, q*, r*) maximizes social welfare (12)–(13)
-- statement:
--   Standing assumptions (Su pp. 6–7): market demand $X \sim D$ with $X \ge 0$; consumer valuations $V \sim \nu$ with finite mean $\mu = EV$; unit cost $c$ and salvage value $s$ with $0 \le s < c < \mu$. Let $F$ be the distribution function of $D$, $\bar F = 1 - F$, and $SW(p,q,r)$ the social welfare (12)–(13) under demand rule (6). Let $q^*$ satisfy
--   $$\bar F(q^*) = \frac{c - s}{E\max(V, s) - s}.$$
--   Then for every price $p$, refund $r$ and stocking quantity $q \ge 0$,
--   $$SW(p, q, r) \le SW\big(E\max(V, s),\, q^*,\, s\big).$$
--
--   This is Corollary 2: the profit-maximizing policy of Proposition 2 also maximizes the sum of consumer surplus and seller profit, so with valuation uncertainty resolved after purchase, monopoly pricing causes no welfare loss.
--
--   **Formalization Note** Welfare carries the demand rule (6): at a price above the reservation price $E\max(V,r)$ nobody buys and the welfare is $-(c-s)q$. Only optimality is claimed, not uniqueness. Demand is assumed nonnegative ($D((-\infty,0)) = 0$) and stocking quantities range over $q \ge 0$: the page's demand is "a mass of infinitesimal consumers" and $q$ a "stocking quantity", and without these readings the profit is unbounded (a negative $q$ with a very negative price makes it arbitrarily large). $0 \le s$ is the page's own "$0 \le s \le c$" (p. 26). The valuation law is a general probability measure with integrable identity rather than a density $g$; $\bar G(r) = \mathbb P(V \ge r)$ follows the page's tie rule (keep iff $V \ge r$).
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 13, Corollary 2, welfare (12)–(13); proof p. 27

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.PartialRefunds

theorem corollary2_welfare (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < meanValuation ν)
    (qstar : ℝ) (hq : 1 - cdf D qstar = (c - s) / (reservationPrice ν s - s)) :
    ∀ p r q, 0 ≤ q → welfare ν D c s p q r ≤ welfare ν D c s (reservationPrice ν s) qstar s := by sorry

end SuReturns.PartialRefunds
