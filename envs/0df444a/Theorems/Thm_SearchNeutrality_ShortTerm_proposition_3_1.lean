-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_proposition_3_1
-- name    : SearchNeutrality.ShortTerm.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:38:40.41831+00:00
-- url     : https://prove2.me/theorems/233fe6c7-2170-439e-8a4b-bdddb6c7ab91
-- title:
--   Proposition 3(1), p. 20 — under Condition 1, search neutrality strictly reduces consumer surplus for α near 1/2
-- statement:
--   Let $1>\rho_H>\rho_L>0$ be the match probabilities, $r\in[0,1]$ the commission rate, and assume Condition 1 ($r\le0.64\rho_L/\rho_H$ and $\rho_L\le0.975$). Then there exist thresholds $\underline\alpha$ and $\bar\alpha$, depending only on $(\rho_H,\rho_L,r)$, with
--   $$
--   \underline\alpha<\frac{\rho_L^2(1-r\rho_H)}{\rho_L^2(1-r\rho_H)+\rho_H}<\frac12<\frac{\rho_H}{\rho_H+\rho_L^2}<\bar\alpha ,
--   $$
--   such that for every popularity $\alpha\in[0,1]$ with $\underline\alpha<\alpha<\bar\alpha$, every equilibrium $(q_F,q_T)$ with search neutrality and every equilibrium $(p_F,p_T,\sigma)$ without it satisfy
--   $$
--   CS^{S}(q_F,q_T)<CS^{NS}(p_F,p_T),
--   $$
--   where $CS^{NS}$ is computed at the ranking the platform chooses at $(p_F,p_T)$.
--
--   This is the central result of the paper's short-term analysis: a regulation that forces relevance-based rankings lowers consumer welfare when the two products are similarly popular, because it lets each seller act as a local monopolist for the consumers to whom its product is shown first.
--
--   **Formalization Note** The thresholds are quantified after $(\rho_H,\rho_L,r)$ and before $\alpha$. The two inner bounds are part of the claim, so the interval $(\underline\alpha,\bar\alpha)$ strictly contains $[\alpha_2^S,\alpha_3^S]$. The comparison is between every equilibrium with and every equilibrium without neutrality; the paper asserts that both are unique (pp. 16–17), and their existence is part of the milestones Proposition 1 and Proposition 2, so the statement is not vacuous.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), p. 20, Proposition 3(1)

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model

namespace SearchNeutrality.ShortTerm

/-- Proposition 3(1) (p. 20): under Condition 1 there are thresholds `α̲` and `ᾱ` with
`α̲ < ρ_L²(1 − rρ_H)/(ρ_L²(1 − rρ_H) + ρ_H) < 1/2 < ρ_H/(ρ_H + ρ_L²) < ᾱ` such that, for every
`α ∈ [0,1]` with `α̲ < α < ᾱ`, consumer surplus in every equilibrium with search neutrality is
strictly smaller than in every equilibrium without it. -/
theorem proposition_3_1 (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hC : Condition1 ρH ρL r) :
    ∃ αlo αhi : ℝ,
      αlo < ρL ^ 2 * (1 - r * ρH) / (ρL ^ 2 * (1 - r * ρH) + ρH) ∧
      ρL ^ 2 * (1 - r * ρH) / (ρL ^ 2 * (1 - r * ρH) + ρH) < 1 / 2 ∧
      1 / 2 < ρH / (ρH + ρL ^ 2) ∧ ρH / (ρH + ρL ^ 2) < αhi ∧
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 → αlo < α → α < αhi →
        ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r α pF pT σ →
        ∀ qF qT : ℝ, IsSEquilibrium ρH ρL r α qF qT →
          consumerSurplus ρH ρL α neutral qF qT < consumerSurplus ρH ρL α (σ pF pT) pF pT := by sorry

end SearchNeutrality.ShortTerm
