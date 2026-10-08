-- Prove2me | Theorems.Thm_SuReturns_PartialRefunds_corollary1_partial_beats_full
-- name    : SuReturns.PartialRefunds.corollary1_partial_beats_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:08.668077+00:00
-- url     : https://prove2.me/theorems/00fb6d13-8895-4eb2-8afb-c9bc6b7cca70
-- title:
--   Corollary 1, p. 12 — optimal profit and optimal quantity are higher under partial refunds than under full refunds
-- statement:
--   Standing assumptions (Su pp. 6–7): market demand $X \sim D$ with $X \ge 0$; consumer valuations $V \sim \nu$ with finite mean $\mu = EV$; unit cost $c$ and salvage value $s$ with $0 \le s < c < \mu$. Let $F$ be the distribution function of $D$, $\bar F = 1 - F$, $\bar G(p) = \mathbb P(V \ge p)$, $\Pi$ the seller's profit (7) under demand rule (6), and $\Pi_{\text{full}}$ the full-refund profit (1). Let $(p^*_F, q^*_F)$ be the full-refund policy of Proposition 1(i): $p^*_F$ maximizes $(p - s)\bar G(p)$ over all real $p$ and $\bar F(q^*_F) = (c-s)/((p^*_F - s)\bar G(p^*_F))$. Let $q^*_P$ be the quantity of Proposition 2: $\bar F(q^*_P) = (c-s)/(E\max(V,s) - s)$. Then
--   1. for every price $p$ and every $q \ge 0$, $\Pi_{\text{full}}(p, q) \le \Pi\big(E\max(V,s),\, q^*_P,\, s\big)$, so the optimal partial-refund profit is at least the profit of every full-refund policy;
--   2. if $F$ is strictly increasing on $[0,\infty)$, then
--   $$q^*_F \le q^*_P.$$
--
--   This is Corollary 1: partial refunds raise both the seller's expected profit and the stocking level.
--
--   **Formalization Note** Part 2 assumes $F$ strictly increasing on $[0,\infty)$; the page's proof inverts $\bar F$ (it writes $\bar F^{-1}$ on p. 27), which presumes this. Without it part 2 is false: on a flat stretch of $F$ the two fractile equations can have the same solution set and any $q^*_F > q^*_P$ from it satisfies both. "Higher" is read as "at least as high", as in the page's proof ($\Pi^*_P \ge \Pi^*_F$, $q^*_P \ge q^*_F$). Demand is assumed nonnegative ($D((-\infty,0)) = 0$) and stocking quantities range over $q \ge 0$: the page's demand is "a mass of infinitesimal consumers" and $q$ a "stocking quantity", and without these readings the profit is unbounded (a negative $q$ with a very negative price makes it arbitrarily large). $0 \le s$ is the page's own "$0 \le s \le c$" (p. 26). The valuation law is a general probability measure with integrable identity rather than a density $g$; $\bar G(r) = \mathbb P(V \ge r)$ follows the page's tie rule (keep iff $V \ge r$).
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 12, Corollary 1; proof p. 26

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.PartialRefunds

theorem corollary1_partial_beats_full (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < meanValuation ν)
    (pF qF : ℝ) (hp : IsMaxOn (fun p => (p - s) * keepProb ν p) Set.univ pF)
    (hqF : 1 - cdf D qF = (c - s) / ((pF - s) * keepProb ν pF))
    (qP : ℝ) (hqP : 1 - cdf D qP = (c - s) / (reservationPrice ν s - s)) :
    (∀ p q, 0 ≤ q →
        fullRefundProfit ν D c s p q ≤ profit ν D c s (reservationPrice ν s) qP s) ∧
      (StrictMonoOn (cdf D) (Set.Ici 0) → qF ≤ qP) := by sorry

end SuReturns.PartialRefunds
