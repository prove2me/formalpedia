-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_s_case_B2
-- name    : SearchNeutrality.ShortTerm.s_case_B2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:39:41.916679+00:00
-- url     : https://prove2.me/theorems/89fe8d56-1e93-40b2-a31b-a73a465eac3f
-- title:
--   Appendix, p. 45, case (B2) — exactly for α₃^S < α ≤ α₄ the equilibrium with neutrality is p_F = 1, p_T = 1/2 + ρ_H(1−α)/(2αρ_L²)
-- statement:
--   Let $1>\rho_H>\rho_L>0$, $r\in[0,1]$, and assume Condition 1. There is a threshold $\alpha_4$ with $\alpha_3^S\le\alpha_4\le1$, where $\alpha_3^S=\rho_H/(\rho_H+\rho_L^2)$, such that for every $\alpha$ with $\alpha_3^S<\alpha\le\alpha_4$ the pair
--   $$
--   p_F=1,\qquad p_T=\frac12+\frac{\rho_H(1-\alpha)}{2\alpha\rho_L^2}
--   $$
--   is an equilibrium with search neutrality, and it is the only one; and for every $\alpha$ with $\alpha_4<\alpha\le1$ no equilibrium with search neutrality has $p_T<p_F=1$. So the case $p_T<p_F=1$ happens exactly when $\alpha_3^S<\alpha\le\alpha_4$.
--
--   Once $F$ is popular enough, the third-party seller, non-prominent for most consumers, cuts its price below the maximum to invite search, while the platform keeps the maximal price.
--
--   **Formalization Note** The threshold $\alpha_4$ is existential: the page's closed form for $\alpha_4^S$ has a misprinted denominator ($r\rho_H^2$ where seller $F$'s no-deviation condition gives $r\rho_H$). The second clause (the case does not happen above $\alpha_4$) is the "only if" of the page's "this case happens if and only if $\alpha_4^S\ge\alpha>\alpha_3^S$"; it pins $\alpha_4$, which otherwise could be taken equal to $\alpha_3^S$ and make the statement empty.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), Appendix, p. 45, case (B2)

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model
import Definitions.Def_SearchNeutrality_ShortTerm_ClosedForms

namespace SearchNeutrality.ShortTerm

/-- Appendix, p. 45, case (B2): under Condition 1 there is `α_4 ∈ [α_3^S, 1]` such that the case
`p_T < p_F = 1` happens if and only if `α_3^S < α ≤ α_4`: for `α_3^S < α ≤ α_4` the unique
equilibrium with search neutrality is `p_F = 1`, `p_T = 1/2 + ρ_H(1 − α)/(2αρ_L²)`, and for
`α_4 < α ≤ 1` no equilibrium with search neutrality has `p_T < p_F = 1`. -/
theorem s_case_B2 (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hC : Condition1 ρH ρL r) :
    ∃ α4 : ℝ, alpha3S ρH ρL ≤ α4 ∧ α4 ≤ 1 ∧
      (∀ α : ℝ, alpha3S ρH ρL < α → α ≤ α4 →
        IsSEquilibrium ρH ρL r α 1 (1 / 2 + ρH * (1 - α) / (2 * α * ρL ^ 2)) ∧
        ∀ pF pT : ℝ, IsSEquilibrium ρH ρL r α pF pT →
          pF = 1 ∧ pT = 1 / 2 + ρH * (1 - α) / (2 * α * ρL ^ 2)) ∧
      ∀ α : ℝ, α4 < α → α ≤ 1 → ∀ pF pT : ℝ, IsSEquilibrium ρH ρL r α pF pT →
        ¬ (pT < pF ∧ pF = 1) := by sorry

end SearchNeutrality.ShortTerm
