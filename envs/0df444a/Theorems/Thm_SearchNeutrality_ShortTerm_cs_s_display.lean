-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_cs_s_display
-- name    : SearchNeutrality.ShortTerm.cs_s_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:39:35.242984+00:00
-- url     : https://prove2.me/theorems/adbf8ad9-c60d-4a3d-9928-c32b556455d6
-- title:
--   Appendix, p. 46 — under the neutral ranking, consumer surplus equals the display CS^S
-- statement:
--   Let $1>\rho_H>\rho_L>0$, $\alpha\in\mathbb R$, and let $p_F,p_T\in[0,1]$. Under the neutral ranking ($F$ prominent for type $f$, $T$ prominent for type $t$), the total consumer surplus — the $\alpha$-weighted average over types of the expected surplus over the search cost $c\sim U[0,1]$ — equals
--   $$
--   \alpha\Bigl[\rho_H(1-p_F)+\frac{(1-\rho_H)\rho_L^2(1-p_T)^2}{2}\Bigr]+(1-\alpha)\Bigl[\rho_H(1-p_T)+\frac{(1-\rho_H)\rho_L^2(1-p_F)^2}{2}\Bigr]+\frac{\rho_H\rho_L^2(p_F-p_T)^2}{2}\bigl[\mathbf 1(p_F\ge p_T)\,\alpha+\mathbf 1(p_F<p_T)(1-\alpha)\bigr].
--   $$
--   In particular it vanishes at $p_F=p_T=1$: when both sellers charge the maximal price, no consumer gains anything.
--
--   **Formalization Note** The page labels this total $CS^{NS}$ and $\mathbb E[CS_f^{NS}]$ where the neutral case is meant, and its per-type formulas for type $t$ exchange $\rho_H$ and $\rho_L$; the total, stated here, is correct.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), Appendix, p. 46, "Equilibrium consumer surplus with search neutrality", total display

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model
import Definitions.Def_SearchNeutrality_ShortTerm_ClosedForms

namespace SearchNeutrality.ShortTerm

/-- Appendix, p. 46: under the search-neutral ranking and prices `p_F, p_T ∈ [0,1]`, the total
consumer surplus (the expectation over the search cost `c ~ U[0,1]`) equals the closed-form
display `CS^S`. -/
theorem cs_s_display (ρH ρL : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (α pF pT : ℝ) (hpF : pF ∈ Set.Icc (0 : ℝ) 1) (hpT : pT ∈ Set.Icc (0 : ℝ) 1) :
    consumerSurplus ρH ρL α neutral pF pT = csS ρH ρL α pF pT := by sorry

end SearchNeutrality.ShortTerm
