-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_s_case_A2
-- name    : SearchNeutrality.ShortTerm.s_case_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:39:24.508978+00:00
-- url     : https://prove2.me/theorems/c654eb48-d30c-428a-845b-682adaaa14bd
-- title:
--   Appendix, p. 45, case (A2) — (p_F, 1) with p_F < 1 is an equilibrium with neutrality iff α < α₂^S, T's deviation polynomial is ≤ 0, and p_F = (1+ρ_H r)/2 + ρ_Hα/(2(1−α)ρ_L²)
-- statement:
--   Let $1>\rho_H>\rho_L>0$, $r\in[0,1]$, assume Condition 1 and let $0\le\alpha\le\frac12$. For a price $p_F$, the pair $(p_F,1)$ with $p_F<1$ is an equilibrium with search neutrality if and only if
--
--   1. $\alpha<\alpha_2^S=\dfrac{\rho_L^2(1-r\rho_H)}{\rho_H+\rho_L^2(1-r\rho_H)}$,
--   2. $2\alpha\rho_L^2-\rho_H[(2-3\rho_L^2)-\alpha(2-5\rho_L^2)]-\rho_H^2[r\rho_L^2+\alpha(1-r\rho_L^2)]\le0$, and
--   3. $$p_F=\frac{1+\rho_H r}{2}+\frac{\rho_H\alpha}{2(1-\alpha)\rho_L^2}.$$
--
--   Condition 2 is the page's simplified form of "seller $T$ does not deviate to a lower price"; condition 1 is "$p_F<1$". This is the region where the third party charges the maximal price and the platform undercuts it.
--
--   **Formalization Note** The page restates condition 2 as $\alpha\ge\alpha_1^S$; the printed $\alpha_1^S$ (with its root $\rho^*$ of $r\rho^3-3\rho^2+2$) does not match the polynomial, so the statement uses the polynomial itself.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), Appendix, p. 45, case (A2) (deviation polynomial from p. 44)

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model
import Definitions.Def_SearchNeutrality_ShortTerm_ClosedForms

namespace SearchNeutrality.ShortTerm

/-- Appendix, p. 45, case (A2): for `α ∈ [0, 1/2]` under Condition 1, `(p_F, 1)` with `p_F < 1` is
an equilibrium with search neutrality iff `α < α_2^S`, seller T's no-deviation polynomial is
`≤ 0`, and `p_F = (1 + ρ_H r)/2 + ρ_H α/(2(1 − α)ρ_L²)`. -/
theorem s_case_A2 (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hC : Condition1 ρH ρL r)
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) (pF : ℝ) :
    (pF < 1 ∧ IsSEquilibrium ρH ρL r α pF 1) ↔
      (α < alpha2S ρH ρL r ∧ devPolyA2 ρH ρL r α ≤ 0 ∧
        pF = (1 + ρH * r) / 2 + ρH * α / (2 * (1 - α) * ρL ^ 2)) := by sorry

end SearchNeutrality.ShortTerm
