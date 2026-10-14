-- Prove2me | Theorems.Thm_SearchNeutrality_Commission_ns_fixed_equilibrium_half
-- name    : SearchNeutrality.Commission.ns_fixed_equilibrium_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:39:26.027511+00:00
-- url     : https://prove2.me/theorems/5509c099-a686-4192-b7ac-4147638f922d
-- title:
--   Appendix, pp. 42–43, (A)/(B) at α = 1/2 — with F prominent for all, the price equilibrium is interior iff r < 3 − 2/(ρ_Hρ_L), and (1, 1/2) otherwise
-- statement:
--   Let $0<\rho_L<\rho_H<1$, $r\in[0,1)$ and $\alpha=1/2$. Consider the pricing game in which product $F$ is prominent for **all** consumers, the ranking being held fixed, and both prices range over $[0,1]$. Let $p_F^{NS*},p_T^{NS*}$ be the interior closed forms of the Appendix (p. 43) evaluated at $\alpha=1/2$. Then $(p_F,p_T)$ is a price equilibrium of this game if and only if
--   $$\Bigl(r<3-\tfrac{2}{\rho_H\rho_L}\ \text{and}\ (p_F,p_T)=(p_F^{NS*},p_T^{NS*})\Bigr)\quad\text{or}\quad\Bigl(r\ge 3-\tfrac{2}{\rho_H\rho_L}\ \text{and}\ (p_F,p_T)=(1,\tfrac12)\Bigr).$$
--
--   This is the Appendix's case analysis (A) $p_F<1$ / (B) $p_F=1$ at equal popularity; at $\alpha=1/2$ the threshold condition $\alpha<\alpha_1^{NS}$ reduces to $r<3-2/(\rho_H\rho_L)$. It supplies the prices that Proposition 4(2) attributes to the market without neutrality.
--
--   **Formalization Note** The Appendix closes with "under Condition 1, there exists a unique pure-strategy equilibrium"; the case analysis (A)–(B) of this fixed-ranking game does not use Condition 1, and §4.2 (p. 23) asserts equilibrium existence for every $r$ at $\alpha=1/2$, so Condition 1 is not assumed here. The (B) paragraph prints the third party's profit with the coefficient of the $p_F<p_T$ branch of demand; the correct coefficient at $p_T\le p_F=1$ is $[\alpha\rho_L^2+(1-\alpha)\rho_H^2]$, which leaves the conclusion $p_T=1/2$ unchanged. At $\alpha=1/2$ the equivalence $\alpha<\alpha_1^{NS}\iff r<3-2/(\rho_H\rho_L)$ follows from the corrected condition $(\rho_H-\rho_L)(2+(3-r)\rho_H\rho_L)+2\rho_L(2-(3-r)\rho_H^2)<0$.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), pp. 42–43, Appendix, Case NS, parts (A) and (B) and display "Equilibrium prices without search neutrality", at α = 1/2

import Mathlib
import Definitions.Def_SearchNeutrality_Commission_Model
import Definitions.Def_SearchNeutrality_Commission_ClosedForms

namespace SearchNeutrality.Commission

/-- Appendix, pp. 42–43, cases (A) and (B) at `α = 1/2`: with product `F` prominent for all
consumers, the price equilibria are exactly the interior closed form `(p_F^{NS*}, p_T^{NS*})`
when `r < 3 - 2/(ρ_H ρ_L)`, and `(1, 1/2)` when `r ≥ 3 - 2/(ρ_H ρ_L)`. -/
theorem ns_fixed_equilibrium_half (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (pF pT : ℝ) :
    IsPriceEquilibrium ρH ρL r (1 / 2) fPrimeAll pF pT ↔
      (r < 3 - 2 / (ρH * ρL) ∧ pF = pFNS ρH ρL r (1 / 2) ∧ pT = pTNS ρH ρL r (1 / 2)) ∨
      (3 - 2 / (ρH * ρL) ≤ r ∧ pF = 1 ∧ pT = 1 / 2) := by sorry

end SearchNeutrality.Commission
