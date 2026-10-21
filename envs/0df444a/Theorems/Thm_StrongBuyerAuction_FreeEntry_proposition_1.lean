-- Prove2me | Theorems.Thm_StrongBuyerAuction_FreeEntry_proposition_1
-- name    : StrongBuyerAuction.FreeEntry.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:00.095379+00:00
-- url     : https://prove2.me/theorems/2a7447cc-dafb-4ccf-b601-c60e6adac57a
-- title:
--   Proposition 1, p. 14 (PDF 15) — a stronger buyer lowers free-entry seller revenue (corrected strictness)
-- statement:
--   Let $F$ be the regular buyers' value distribution function and $G,G'$ the original and improved strong-buyer distributions, all from probability laws on $[0,1]$. Assume $G$ strictly first-order stochastically dominates $F$ and $G'$ strictly dominates $G$. Suppose $G'(z)<G(z)$ on a positive-measure set where $F(z)<1$. For any entry cost $c>0$ and any real free-entry roots $N_G,N_{G'}\ge1$, satisfying $\pi(N_G\mid G)=\pi(N_{G'}\mid G')=c$, the seller's expected revenue satisfies
--
--   $$R(N_{G'}\mid G')<R(N_G\mid G).$$
--
--   The theorem records the paper's reversal: improving the strong buyer depresses seller revenue when regular entry adjusts to the zero-profit condition.
--
--   **Formalization Note** The extra strictness guard is required because the printed FOSD condition allows $G'<G$ only where $F=1$, which changes neither regular-buyer profit nor free-entry revenue. The counts are real, following the paper's explicit choice to ignore integer constraints.
-- source:
--   Marquez & Singh, Selling assets: Are sellers better off with strong buyers?, SSRN working paper 3949699 (October 2021), p. 14 (PDF 15), Proposition 1 (corrected strictness guard)

import Mathlib
import Definitions.Def_StrongBuyerAuction_FreeEntry_Model

open MeasureTheory ProbabilityTheory

namespace StrongBuyerAuction.FreeEntry

/-- Proposition 1, p. 14, corrected by requiring the shift where regular buyers can win. -/
theorem proposition_1 (μF μG μG' : Measure ℝ)
    (hμF : IsValueLaw μF) (hμG : IsValueLaw μG) (hμG' : IsValueLaw μG')
    (c : ℝ) (hc : 0 < c)
    (hGF : FOSD (cdf μG) (cdf μF))
    (hG'G : FOSD (cdf μG') (cdf μG))
    (hguard : StrictWhereOpen (cdf μF) (cdf μG') (cdf μG))
    (NG NG' : ℝ)
    (hNG : IsFreeEntry (cdf μF) (cdf μG) c NG)
    (hNG' : IsFreeEntry (cdf μF) (cdf μG') c NG') :
    rev (cdf μF) (cdf μG') NG' < rev (cdf μF) (cdf μG) NG := by sorry

end StrongBuyerAuction.FreeEntry
