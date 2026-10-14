-- Prove2me | Theorems.Thm_SearchNeutrality_Commission_cs_ns_display_half
-- name    : SearchNeutrality.Commission.cs_ns_display_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:39:33.073007+00:00
-- url     : https://prove2.me/theorems/06624e3d-578e-43f9-bb69-6f647d619075
-- title:
--   Appendix, pp. 43–44 at α = 1/2 — consumer surplus with F prominent for all equals the display CS^{NS} when p_T ≤ p_F
-- statement:
--   Let $0<\rho_L<\rho_H<1$, $\alpha=1/2$, and let $0\le p_T\le p_F\le 1$. When product $F$ is prominent for all consumers, the total consumer surplus — the average over the two types of the expected optimal-search payoff, with search cost $c\sim U[0,1]$ for the non-prominent product — equals
--   $$CS^{NS}=\tfrac12(\rho_H+\rho_L)(1-p_F)+\frac{\rho_L^2}{4}\bigl[\rho_H(p_F-p_T)^2+(1-\rho_H)(1-p_T)^2\bigr]+\frac{\rho_H^2}{4}\bigl[\rho_L(p_F-p_T)^2+(1-\rho_L)(1-p_T)^2\bigr].$$
--
--   This is the Appendix's display for consumer surplus without search neutrality, at equal popularity; it turns the comparison of consumer surplus in Proposition 5 into a comparison of explicit functions of the prices.
--
--   **Formalization Note** Consumer surplus is defined from the search model as an integral over $c\in[0,1]$, not by this formula. The paper's display is stated for general $\alpha$; this item is its $\alpha=1/2$ instance (the companion mission states the general version).
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), pp. 43–44, Appendix, "Equilibrium consumer surplus without search neutrality", at α = 1/2

import Mathlib
import Definitions.Def_SearchNeutrality_Commission_Model
import Definitions.Def_SearchNeutrality_Commission_ClosedForms

namespace SearchNeutrality.Commission

/-- Appendix, pp. 43–44, at `α = 1/2`: with `F` prominent for all consumers and
`0 ≤ p_T ≤ p_F ≤ 1`, the consumer surplus equals the display `CS^{NS}`. -/
theorem cs_ns_display_half (ρH ρL : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (pF pT : ℝ) (hpF : pF ∈ Set.Icc (0 : ℝ) 1) (hpT : pT ∈ Set.Icc (0 : ℝ) 1) (hle : pT ≤ pF) :
    consumerSurplus ρH ρL (1 / 2) fPrimeAll pF pT = csNS ρH ρL (1 / 2) pF pT := by sorry

end SearchNeutrality.Commission
