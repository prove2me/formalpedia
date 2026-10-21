-- Prove2me | Theorems.Thm_StrongBuyerAuction_FreeEntry_eq_10
-- name    : StrongBuyerAuction.FreeEntry.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:56.381809+00:00
-- url     : https://prove2.me/theorems/ac070909-797c-4ff3-9f61-6f4e8554bc8d
-- title:
--   Proof of Proposition 1, p. 39 (PDF 40), display (10) — positive revenue derivative at free entry
-- statement:
--   Let $F$ and $G$ be value distribution functions on $[0,1]$, with $G$ strictly dominating $F$, and let $c>0$. Assume $G>0$ and $F<1$ on a positive-measure set. If $N_G\ge1$ satisfies $\pi(N_G\mid G)=c$, define $H(N)=1-\int_0^1 F(z)^N\,dz-Nc$. The derivative exists at $N_G$ and
--
--   $$H'(N_G)=-\int_0^1 F(z)^{N_G}\log F(z)\,dz-c
--   =-\int_0^1 F(z)^{N_G}\log F(z)\,dz-\pi(N_G\mid G)>0.$$
--
--   This is the local positive-slope calculation in the proof of Proposition 1.
--
--   **Formalization Note** Real powers are used for the paper's continuous buyer count. At a zero CDF value, $F^N\log F$ is interpreted as zero. The nondegeneracy guard makes the claimed sign strict.
-- source:
--   Marquez & Singh, Selling assets: Are sellers better off with strong buyers?, SSRN working paper 3949699 (October 2021), p. 39 (PDF 40), proof of Proposition 1, display (10) and closing sentence

import Mathlib
import Definitions.Def_StrongBuyerAuction_FreeEntry_Model

open MeasureTheory ProbabilityTheory

namespace StrongBuyerAuction.FreeEntry

/-- Display (10), p. 39: derivative at the free-entry root and its positive sign. -/
theorem eq_10 (μF μG : Measure ℝ)
    (hμF : IsValueLaw μF) (hμG : IsValueLaw μG)
    (c : ℝ) (hc : 0 < c)
    (hGF : FOSD (cdf μG) (cdf μF))
    (hnd : ProfitNondegenerate (cdf μF) (cdf μG))
    (NG : ℝ) (hNG : IsFreeEntry (cdf μF) (cdf μG) c NG) :
    HasDerivAt
      (fun N : ℝ => 1 - (∫ z in (0 : ℝ)..1, (cdf μF z) ^ N) - N * c)
      (-(∫ z in (0 : ℝ)..1, (cdf μF z) ^ NG * Real.log (cdf μF z)) - c) NG ∧
    0 < -(∫ z in (0 : ℝ)..1, (cdf μF z) ^ NG * Real.log (cdf μF z)) -
      piReg (cdf μF) (cdf μG) NG := by sorry

end StrongBuyerAuction.FreeEntry
