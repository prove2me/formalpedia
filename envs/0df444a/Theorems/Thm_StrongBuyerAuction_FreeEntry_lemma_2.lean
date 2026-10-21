-- Prove2me | Theorems.Thm_StrongBuyerAuction_FreeEntry_lemma_2
-- name    : StrongBuyerAuction.FreeEntry.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:49.652783+00:00
-- url     : https://prove2.me/theorems/c839cf34-700c-4265-a24e-49afcd51814f
-- title:
--   Lemma 2, p. 13 (PDF 14) — a stronger buyer reduces free entry
-- statement:
--   Let $F,G,G'$ be value distribution functions on $[0,1]$. Assume $G$ strictly dominates $F$ and $G'$ strictly dominates $G$ in first-order stochastic dominance, with a positive-measure strict shift where $F<1$. For an entry cost $c>0$, let $N_G$ and $N_{G'}$ be any real free-entry roots at least one, so $\pi(N_G\mid G)=\pi(N_{G'}\mid G')=c$. Then
--
--   $$N_{G'}<N_G.$$
--
--   This comparison is the entry response to a stronger bidder and a prerequisite of Proposition 1.
--
--   **Formalization Note** The roots are supplied as witnesses of the paper's zero-profit equations. No default-valued real infimum is used. The strict-shift guard is necessary for the paper's strict profit premise.
-- source:
--   Marquez & Singh, Selling assets: Are sellers better off with strong buyers?, SSRN working paper 3949699 (October 2021), p. 13 (PDF 14), Lemma 2 and eq. (4)

import Mathlib
import Definitions.Def_StrongBuyerAuction_FreeEntry_Model

open MeasureTheory ProbabilityTheory

namespace StrongBuyerAuction.FreeEntry

/-- Lemma 2, p. 13: a stronger buyer reduces free entry. -/
theorem lemma_2 (μF μG μG' : Measure ℝ)
    (hμF : IsValueLaw μF) (hμG : IsValueLaw μG) (hμG' : IsValueLaw μG')
    (c : ℝ) (hc : 0 < c)
    (hGF : FOSD (cdf μG) (cdf μF))
    (hG'G : FOSD (cdf μG') (cdf μG))
    (hguard : StrictWhereOpen (cdf μF) (cdf μG') (cdf μG))
    (NG NG' : ℝ)
    (hNG : IsFreeEntry (cdf μF) (cdf μG) c NG)
    (hNG' : IsFreeEntry (cdf μF) (cdf μG') c NG') :
    NG' < NG := by sorry

end StrongBuyerAuction.FreeEntry
