-- Prove2me | Theorems.Thm_StrongBuyerAuction_FreeEntry_lemma_1_dominance
-- name    : StrongBuyerAuction.FreeEntry.lemma_1_dominance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:45.774241+00:00
-- url     : https://prove2.me/theorems/ce5c5edd-f680-454c-8ffe-dd3e0190c382
-- title:
--   Lemma 1, pp. 11–12 (PDF 12–13) — regular-buyer profit falls as the strong buyer improves
-- statement:
--   Let $F,G,G'$ be value distribution functions on $[0,1]$. Assume $G$ strictly dominates $F$ and $G'$ strictly dominates $G$ in first-order stochastic dominance. If the change $G'<G$ occurs on a positive-measure set where $F<1$, then for every real $N\ge1$ and entry cost $c>0$,
--
--   $$\pi(N\mid G')<\pi(N\mid G).$$
--
--   This is the profit comparison in Lemma 1, which supplies the strict comparison needed for free entry. The fixed-entry seller-revenue clause is outside this milestone.
--
--   **Formalization Note** The added condition locates the strict CDF shift where a regular buyer can still win. A shift only where $F=1$ leaves both profits equal, despite strict FOSD as printed.
-- source:
--   Marquez & Singh, Selling assets: Are sellers better off with strong buyers?, SSRN working paper 3949699 (October 2021), pp. 11–12 (PDF 12–13), Lemma 1, dominance-profit clause; proof p. 37 (PDF 38)

import Mathlib
import Definitions.Def_StrongBuyerAuction_FreeEntry_Model

open MeasureTheory ProbabilityTheory

namespace StrongBuyerAuction.FreeEntry

/-- Profit half of Lemma 1, pp. 11–12: a stronger bidder lowers regular-bidder profit. -/
theorem lemma_1_dominance (μF μG μG' : Measure ℝ)
    (hμF : IsValueLaw μF) (hμG : IsValueLaw μG) (hμG' : IsValueLaw μG')
    (c : ℝ) (hc : 0 < c)
    (hGF : FOSD (cdf μG) (cdf μF))
    (hG'G : FOSD (cdf μG') (cdf μG))
    (hguard : StrictWhereOpen (cdf μF) (cdf μG') (cdf μG))
    (N : ℝ) (hN : 1 ≤ N) :
    piReg (cdf μF) (cdf μG') N < piReg (cdf μF) (cdf μG) N := by sorry

end StrongBuyerAuction.FreeEntry
