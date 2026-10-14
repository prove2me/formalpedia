-- Prove2me | Theorems.Thm_SearchNeutrality_Commission_proposition_4_1
-- name    : SearchNeutrality.Commission.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:38:30.089908+00:00
-- url     : https://prove2.me/theorems/515d92ea-58e3-473f-93cb-b452f8554c87
-- title:
--   Proposition 4(1), p. 24 — at α = 1/2 and r ≥ ρ_L/ρ_H, without neutrality the platform ranks neutrally and p_F = p_T = 1
-- statement:
--   Let $0<\rho_L<\rho_H<1$, $r\in[0,1)$, and $\alpha=1/2$, and consider the market **without** search neutrality: the sellers set prices in $[0,1]$, and the platform then chooses, for each consumer type, the prominent product that maximizes its own profit (an optimal ranking rule $\sigma$, applied also at deviation prices).
--
--   1. If $r>\rho_L/\rho_H$, an equilibrium exists, and in every equilibrium $(p_F,p_T,\sigma)$ the platform makes $F$ prominent for type $f$ and $T$ prominent for type $t$, and
--   $$p_F^{NS*}=p_T^{NS*}=1 .$$
--   2. If $r=\rho_L/\rho_H$, there is an equilibrium with these prices and this ranking.
--
--   When the commission is high, the platform earns enough on product $T$ that it has no reason to steer type-$t$ consumers away from it, so the outcome coincides with the neutral one.
--
--   **Formalization Note** The paper states the result for $r\ge\rho_L/\rho_H$. At $r=\rho_L/\rho_H$ the platform is indifferent between the two rankings for type-$t$ consumers at prices $(1,1)$; a ranking rule that breaks that tie toward $F$ supports a different equilibrium, so at the boundary only existence is claimed. "The equilibrium prices are" is read as "every equilibrium has these prices", and the ranking claim is about $\sigma$ at the equilibrium prices. $r<1$ is a disclosed reading (at $r=1$ the third party is indifferent among all prices).
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), p. 24, Proposition 4(1)

import Mathlib
import Definitions.Def_SearchNeutrality_Commission_Model

namespace SearchNeutrality.Commission

/-- Proposition 4(1), p. 24: at `α = 1/2` without search neutrality, for `r > ρ_L/ρ_H` an
equilibrium exists and every equilibrium has the neutral ranking and prices `p_F = p_T = 1`;
at the boundary `r = ρ_L/ρ_H` such an equilibrium exists. -/
theorem proposition_4_1 (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (ρL / ρH < r →
      (∃ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ) ∧
      ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ →
        σ pF pT = neutral ∧ pF = 1 ∧ pT = 1) ∧
    (r = ρL / ρH →
      ∃ σ : ℝ → ℝ → Ranking, IsNSEquilibrium ρH ρL r (1 / 2) 1 1 σ ∧ σ 1 1 = neutral) := by sorry

end SearchNeutrality.Commission
