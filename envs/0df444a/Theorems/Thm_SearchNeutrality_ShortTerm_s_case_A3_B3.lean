-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_s_case_A3_B3
-- name    : SearchNeutrality.ShortTerm.s_case_A3_B3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:39:29.855993+00:00
-- url     : https://prove2.me/theorems/386422ca-97ba-484d-acbe-e3f4dc05a9ae
-- title:
--   Appendix, pp. 45–46, cases (A3) and (B3) — for α₂^S ≤ α ≤ α₃^S the unique equilibrium with neutrality is p_F = p_T = 1
-- statement:
--   Let $1>\rho_H>\rho_L>0$, $r\in[0,1]$, assume Condition 1, and let $\alpha\in[0,1]$ with
--   $$
--   \alpha_2^S=\frac{\rho_L^2(1-r\rho_H)}{\rho_H+\rho_L^2(1-r\rho_H)}\;\le\;\alpha\;\le\;\alpha_3^S=\frac{\rho_H}{\rho_H+\rho_L^2}.
--   $$
--   Then $(p_F,p_T)=(1,1)$ is an equilibrium with search neutrality, and every equilibrium with search neutrality equals $(1,1)$.
--
--   When the two products are similarly popular, neutrality lets each seller act as a local monopolist for the type for which its product is prominent, and both charge the maximal price. At these prices consumers obtain zero surplus, which is the fact the goal theorem builds on.
--
--   **Formalization Note** The page's (A3) has the strict bound $\alpha>\alpha_2^S$; at $\alpha=\alpha_2^S$ the (A2) price equals $1$, so $(1,1)$ is the equilibrium there too, and the statement includes the endpoint. Only the direction "(1,1) is the unique equilibrium on this interval" is stated, not the converse.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), Appendix, p. 45, case (A3) and definition of α_3^S in (B2); p. 46, case (B3)

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model
import Definitions.Def_SearchNeutrality_ShortTerm_ClosedForms

namespace SearchNeutrality.ShortTerm

/-- Appendix, pp. 45–46, cases (A3) and (B3): under Condition 1, for `α_2^S ≤ α ≤ α_3^S` the
prices `p_F = p_T = 1` form an equilibrium with search neutrality, and it is the only one. -/
theorem s_case_A3_B3 (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hC : Condition1 ρH ρL r)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (h2 : alpha2S ρH ρL r ≤ α) (h3 : α ≤ alpha3S ρH ρL) :
    IsSEquilibrium ρH ρL r α 1 1 ∧
      ∀ pF pT : ℝ, IsSEquilibrium ρH ρL r α pF pT → pF = 1 ∧ pT = 1 := by sorry

end SearchNeutrality.ShortTerm
