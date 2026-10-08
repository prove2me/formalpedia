-- Prove2me | Theorems.Thm_SuReturns_PartialRefunds_proposition2_optimal_policy
-- name    : SuReturns.PartialRefunds.proposition2_optimal_policy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:10.452163+00:00
-- url     : https://prove2.me/theorems/8a871e39-9c78-4071-af14-6c14b261a8c1
-- title:
--   Proposition 2, p. 11 — p* = E max(V, s), F̄(q*) = (c − s)/(p* − s), r* = s are optimal
-- statement:
--   Standing assumptions (Su pp. 6–7): market demand $X \sim D$ with $X \ge 0$; consumer valuations $V \sim \nu$ with finite mean $\mu = EV$; unit cost $c$ and salvage value $s$ with $0 \le s < c < \mu$. Let $F$ be the distribution function of $D$ and $\bar F = 1 - F$, and let $\Pi(p,q,r)$ be the seller's expected profit (7)–(8) under the demand rule (6), where consumers buy only if $p \le E\max(V,r)$. Set
--   $$p^* = E\max(V, s), \qquad r^* = s,$$
--   and let $q^*$ be any quantity with
--   $$\bar F(q^*) = \frac{c - s}{p^* - s} = \frac{c - s}{E\max(V, s) - s}.$$
--   Then for every price $p$, every refund $r$ and every stocking quantity $q \ge 0$,
--   $$\Pi(p, q, r) \le \Pi(p^*, q^*, r^*).$$
--
--   This is Proposition 2: with valuations learned after purchase, the seller optimally charges consumers their full reservation price, sets the refund equal to the salvage value, which implements the efficient ex post allocation of the good, and stocks the newsvendor quantity at margin $E\max(V,s) - s$. It is the basis for the comparison with full refunds (Corollary 1), the welfare result (Corollary 2) and the coordination results of Section 5.
--
--   **Formalization Note** The triple is stated in the page's closed form and its optimality is claimed; uniqueness is not (if $\nu$ puts no mass on $[s, r)$, the refund $r$ is optimal too). The denominator $E\max(V,s) - s \ge \mu - s > 0$. Existence of $q^*$ is not claimed; for a continuous demand law it exists by the newsvendor theorem referenced in this mission. Any $q^*$ solving (10) is automatically $\ge 0$, since $\bar F = 1$ on $(-\infty, 0)$. Demand is assumed nonnegative ($D((-\infty,0)) = 0$) and stocking quantities range over $q \ge 0$: the page's demand is "a mass of infinitesimal consumers" and $q$ a "stocking quantity", and without these readings the profit is unbounded (a negative $q$ with a very negative price makes it arbitrarily large). $0 \le s$ is the page's own "$0 \le s \le c$" (p. 26). The valuation law is a general probability measure with integrable identity rather than a density $g$; $\bar G(r) = \mathbb P(V \ge r)$ follows the page's tie rule (keep iff $V \ge r$).
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 11, Proposition 2, (9)–(11); profit (7)–(8), p. 11; demand (6), p. 10

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.PartialRefunds

theorem proposition2_optimal_policy (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < meanValuation ν)
    (qstar : ℝ) (hq : 1 - cdf D qstar = (c - s) / (reservationPrice ν s - s)) :
    ∀ p r q, 0 ≤ q → profit ν D c s p q r ≤ profit ν D c s (reservationPrice ν s) qstar s := by sorry

end SuReturns.PartialRefunds
