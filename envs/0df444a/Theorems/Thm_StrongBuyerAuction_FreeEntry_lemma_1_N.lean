-- Prove2me | Theorems.Thm_StrongBuyerAuction_FreeEntry_lemma_1_N
-- name    : StrongBuyerAuction.FreeEntry.lemma_1_N
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:52.046464+00:00
-- url     : https://prove2.me/theorems/07dfb13f-19fb-4648-a45b-734f8f1db845
-- title:
--   Lemma 1, p. 11 (PDF 12) — regular-buyer profit falls with the number of buyers
-- statement:
--   Let $F$ and $G$ be the regular and strong buyers' value distribution functions on $[0,1]$, with $G$ strictly first-order stochastically dominating $F$. Let the entry cost satisfy $c>0$. Suppose $G(z)>0$ and $F(z)<1$ simultaneously on a set of positive Lebesgue measure. For real $1\le N<N'$, the regular buyer's gross expected profit obeys
--
--   $$\pi(N'\mid G)<\pi(N\mid G).$$
--
--   This is the profit clause of Lemma 1, used to compare free-entry roots. The fixed-entry seller-revenue clause is outside this milestone.
--
--   **Formalization Note** The positive-measure condition ensures that the strict inequality has a nonzero integrand. Real buyer counts follow the paper's convention of ignoring integer constraints.
-- source:
--   Marquez & Singh, Selling assets: Are sellers better off with strong buyers?, SSRN working paper 3949699 (October 2021), p. 11 (PDF 12), Lemma 1, profit-in-N clause; proof p. 37 (PDF 38)

import Mathlib
import Definitions.Def_StrongBuyerAuction_FreeEntry_Model

open MeasureTheory ProbabilityTheory

namespace StrongBuyerAuction.FreeEntry

/-- Profit half of Lemma 1, p. 11: extra regular entry lowers a regular bidder's profit. -/
theorem lemma_1_N (μF μG : Measure ℝ)
    (hμF : IsValueLaw μF) (hμG : IsValueLaw μG)
    (c : ℝ) (hc : 0 < c)
    (hGF : FOSD (cdf μG) (cdf μF))
    (hnd : ProfitNondegenerate (cdf μF) (cdf μG))
    (N N' : ℝ) (hN : 1 ≤ N) (hNN' : N < N') :
    piReg (cdf μF) (cdf μG) N' < piReg (cdf μF) (cdf μG) N := by sorry

end StrongBuyerAuction.FreeEntry
