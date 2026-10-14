-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_cs_ns_display
-- name    : SearchNeutrality.ShortTerm.cs_ns_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:39:27.853503+00:00
-- url     : https://prove2.me/theorems/fb336c0b-23ce-4adf-a196-e16fb1e0c39a
-- title:
--   Appendix, pp. 43–44 — with F prominent for all and p_T ≤ p_F, consumer surplus equals the display CS^NS
-- statement:
--   Let $1>\rho_H>\rho_L>0$, $\alpha\in\mathbb R$, and let $0\le p_T\le p_F\le1$. When $F$ is prominent for both consumer types, the total consumer surplus — the $\alpha$-weighted average over types of the expected surplus over the search cost $c\sim U[0,1]$ — equals
--   $$
--   [\alpha\rho_H+(1-\alpha)\rho_L](1-p_F)+\frac{\alpha\rho_L^2}{2}\bigl[\rho_H(p_F-p_T)^2+(1-\rho_H)(1-p_T)^2\bigr]+\frac{(1-\alpha)\rho_H^2}{2}\bigl[\rho_L(p_F-p_T)^2+(1-\rho_L)(1-p_T)^2\bigr].
--   $$
--   This closed form turns the comparison of consumer surplus across regimes into a comparison of explicit expressions in the equilibrium prices.
--
--   **Formalization Note** The identity holds for all such prices, not only at equilibrium; the page's "Since $p_F^{NS*}\ge p_T^{NS*}$" is the hypothesis $p_T\le p_F$. It rests on $\int_0^1(a-c)^+\,dc=a^2/2$ for $a\in[0,1]$.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), Appendix, p. 43 (CS_f^NS), p. 44 (CS_t^NS and total CS^NS), "Equilibrium consumer surplus without search neutrality"

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model
import Definitions.Def_SearchNeutrality_ShortTerm_ClosedForms

namespace SearchNeutrality.ShortTerm

/-- Appendix, pp. 43–44: with `F` prominent for all consumers and prices `0 ≤ p_T ≤ p_F ≤ 1`, the
total consumer surplus (the expectation over the search cost `c ~ U[0,1]`) equals the closed-form
display `CS^{NS}`. -/
theorem cs_ns_display (ρH ρL : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (α pF pT : ℝ) (hpF : pF ∈ Set.Icc (0 : ℝ) 1) (hpT : pT ∈ Set.Icc (0 : ℝ) 1) (hle : pT ≤ pF) :
    consumerSurplus ρH ρL α fPrimeAll pF pT = csNS ρH ρL α pF pT := by sorry

end SearchNeutrality.ShortTerm
