-- Prove2me | Theorems.Thm_SuReturns_PartialRefunds_proposition1_ii_zero_salvage
-- name    : SuReturns.PartialRefunds.proposition1_ii_zero_salvage
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:10.691161+00:00
-- url     : https://prove2.me/theorems/59a622a3-65b0-49f7-9625-861a86b03b79
-- title:
--   Proof of Proposition 1(ii), p. 26 — at s = 0 the seller prefers no returns to full refunds
-- statement:
--   Let market demand $X \sim D$ be nonnegative, let consumer valuations $V \sim \nu$ be nonnegative with finite mean $\mu = EV$, and let the unit cost satisfy $0 < c < \mu$. Take salvage value $s = 0$. With $\Pi_{\text{full}}$ the full-refund profit (1) and $\Pi_{\text{no}}$ the no-returns profit (3), for every price $p$ and every stocking quantity $q \ge 0$,
--   $$\Pi_{\text{full}}(p, q) = p\bar G(p)E\min(X,q) - cq \;\le\; \mu E\min(X,q) - cq = \Pi_{\text{no}}(q).$$
--
--   This is the extreme case $s = 0$ in the proof of Proposition 1(ii): when returned units are worthless, no full-refund policy beats selling without returns.
--
--   **Formalization Note** Valuations are assumed nonnegative ($\nu((-\infty,0)) = 0$): the page integrates valuations from $0$ (p. 24), and the key inequality $\mu \ge p\bar G(p)$ fails for laws with negative mass. The proposition's general form, "when $c$ or $s$ is sufficiently low", is proved on the page only "by continuity" and is not formalized here. Demand is assumed nonnegative and $q \ge 0$, as in the rest of the mission.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 26, proof of Proposition 1(ii), case s = 0; Proposition 1(ii), p. 9

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.PartialRefunds

theorem proposition1_ii_zero_salvage (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hν0 : ν (Set.Iio 0) = 0)
    (hD0 : D (Set.Iio 0) = 0) (c : ℝ) (hc : 0 < c) (hcμ : c < meanValuation ν) :
    ∀ p q, 0 ≤ q → fullRefundProfit ν D c 0 p q ≤ noReturnsProfit ν D c 0 q := by sorry

end SuReturns.PartialRefunds
