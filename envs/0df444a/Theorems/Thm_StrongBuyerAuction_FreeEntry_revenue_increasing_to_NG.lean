-- Prove2me | Theorems.Thm_StrongBuyerAuction_FreeEntry_revenue_increasing_to_NG
-- name    : StrongBuyerAuction.FreeEntry.revenue_increasing_to_NG
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:01.701483+00:00
-- url     : https://prove2.me/theorems/da0ca294-4546-4b16-81c2-d12e56cdd2b0
-- title:
--   Proof of Proposition 1, pp. 38–39 (PDF 39–40) — corrected revenue monotonicity up to free entry
-- statement:
--   Let $F$ and $G$ be value distribution functions on $[0,1]$, with $G$ strictly dominating $F$, and let $c>0$. Assume $G>0$ and $F<1$ on a positive-measure set. If $N_G\ge1$ satisfies $\pi(N_G\mid G)=c$, then the function
--
--   $$N\longmapsto 1-\int_0^1 F(z)^N\,dz-Nc$$
--
--   is strictly increasing for $1\le N\le N_G$. This is the range needed when Proposition 1 compares $N_{G'}<N_G$.
--
--   **Formalization Note** The paper says the function is increasing in $N$ without a range. Globally that is false: for $F(z)=z$ and $c=1/30$, it eventually decreases. The statement uses the interval warranted by the proof's derivative calculation.
-- source:
--   Marquez & Singh, Selling assets: Are sellers better off with strong buyers?, SSRN working paper 3949699 (October 2021), pp. 38–39 (PDF 39–40), proof of Proposition 1, page-break 'it suffices' claim (corrected range)

import Mathlib
import Definitions.Def_StrongBuyerAuction_FreeEntry_Model

open MeasureTheory ProbabilityTheory

namespace StrongBuyerAuction.FreeEntry

/-- Corrected claim in the proof of Proposition 1, pp. 38–39: revenue rises up to N_G. -/
theorem revenue_increasing_to_NG (μF μG : Measure ℝ)
    (hμF : IsValueLaw μF) (hμG : IsValueLaw μG)
    (c : ℝ) (hc : 0 < c)
    (hGF : FOSD (cdf μG) (cdf μF))
    (hnd : ProfitNondegenerate (cdf μF) (cdf μG))
    (NG : ℝ) (hNG : IsFreeEntry (cdf μF) (cdf μG) c NG) :
    StrictMonoOn
      (fun N : ℝ => 1 - (∫ z in (0 : ℝ)..1, (cdf μF z) ^ N) - N * c)
      (Set.Icc 1 NG) := by sorry

end StrongBuyerAuction.FreeEntry
