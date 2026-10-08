-- Prove2me | Theorems.Thm_SuReturns_PartialRefunds_proposition1_full_refund
-- name    : SuReturns.PartialRefunds.proposition1_full_refund
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:00.439988+00:00
-- url     : https://prove2.me/theorems/ad52f79d-6f4d-4328-90e2-505f208d2f1a
-- title:
--   Proposition 1(i), p. 9 — under full refunds, p* = argmax (p − s)Ḡ(p) and F̄(q*) = (c − s)/((p* − s)Ḡ(p*)) are optimal
-- statement:
--   Standing assumptions (Su pp. 6–7): market demand $X \sim D$ with $X \ge 0$; consumer valuations $V \sim \nu$ with finite mean $\mu = EV$; unit cost $c$ and salvage value $s$ with $0 \le s < c < \mu$. Let $\bar G(p) = \mathbb P(V \ge p)$, $F$ the distribution function of $D$ and $\bar F = 1 - F$, and let $\Pi_{\text{full}}(p,q)$ be the full-refund profit (1). Suppose $p^*$ maximizes $(p - s)\bar G(p)$ over all real $p$, (4), and $q^*$ satisfies
--   $$\bar F(q^*) = \frac{c - s}{(p^* - s)\bar G(p^*)}. \qquad (5)$$
--   Then for every price $p$ and every stocking quantity $q \ge 0$,
--   $$\Pi_{\text{full}}(p, q) \le \Pi_{\text{full}}(p^*, q^*).$$
--
--   This is Proposition 1(i): under a full refund policy the seller's price and quantity decisions separate, the price maximizing the per-unit margin $(p - s)\bar G(p)$ and the quantity solving a newsvendor problem with that margin.
--
--   **Formalization Note** The denominator of (5) is positive at a maximizer: since $\mu > s$, some $p > s$ has $\bar G(p) > 0$. Only the sufficiency direction of "characterized by" is stated, and existence of $p^*$, $q^*$ is not claimed; if $(p^* - s)\bar G(p^*) < c - s$, (5) has no solution and the statement is vacuous for that law, a gap of the page itself. Demand is assumed nonnegative ($D((-\infty,0)) = 0$) and stocking quantities range over $q \ge 0$: the page's demand is "a mass of infinitesimal consumers" and $q$ a "stocking quantity", and without these readings the profit is unbounded (a negative $q$ with a very negative price makes it arbitrarily large). $0 \le s$ is the page's own "$0 \le s \le c$" (p. 26). The valuation law is a general probability measure with integrable identity rather than a density $g$; $\bar G(r) = \mathbb P(V \ge r)$ follows the page's tie rule (keep iff $V \ge r$).
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 9, Proposition 1(i), (4)–(5); profit (1)–(2), p. 8

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.PartialRefunds

theorem proposition1_full_refund (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < meanValuation ν)
    (pF qF : ℝ) (hp : IsMaxOn (fun p => (p - s) * keepProb ν p) Set.univ pF)
    (hq : 1 - cdf D qF = (c - s) / ((pF - s) * keepProb ν pF)) :
    ∀ p q, 0 ≤ q → fullRefundProfit ν D c s p q ≤ fullRefundProfit ν D c s pF qF := by sorry

end SuReturns.PartialRefunds
