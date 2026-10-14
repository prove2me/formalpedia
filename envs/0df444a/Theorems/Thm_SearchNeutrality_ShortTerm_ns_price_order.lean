-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_ns_price_order
-- name    : SearchNeutrality.ShortTerm.ns_price_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:38:32.858769+00:00
-- url     : https://prove2.me/theorems/8af4f74d-3f49-4b8e-ad02-8a97ff54ddc3
-- title:
--   Appendix, p. 42 — with F prominent for all consumers, every equilibrium has p_T ≤ p_F
-- statement:
--   Consider the pricing game in which the platform makes its own product $F$ prominent for both consumer types, and let $\alpha\in[0,1]$, $1>\rho_H>\rho_L>0$, $r\in[0,1]$. If $(p_F,p_T)\in[0,1]^2$ is a Nash equilibrium of this game, then
--   $$
--   p_T\le p_F .
--   $$
--   The reason is that when $p_F\le p_T$ the demand for $F$ does not depend on $p_F$, so the platform's profit is strictly increasing in its own price there. This ordering selects the branch of the kinked demands on which the equilibrium is computed.
--
--   **Formalization Note** The ranking is held fixed at "$F$ prominent for all"; the game in which the platform also chooses the ranking is the subject of Lemma A1 and Proposition 1.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), Appendix, p. 42, "Equilibrium derivation for the scenario without search neutrality (Case NS)"

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model

namespace SearchNeutrality.ShortTerm

/-- Appendix, p. 42: when product `F` is prominent for all consumers, every equilibrium of the
pricing game has `p_T ≤ p_F`. -/
theorem ns_price_order (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (pF pT : ℝ)
    (heq : IsPriceEquilibrium ρH ρL r α fPrimeAll pF pT) :
    pT ≤ pF := by sorry

end SearchNeutrality.ShortTerm
