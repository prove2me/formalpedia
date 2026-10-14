-- Prove2me | Theorems.Thm_SearchNeutrality_Commission_proposition_5
-- name    : SearchNeutrality.Commission.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:38:48.088497+00:00
-- url     : https://prove2.me/theorems/073a49f7-3182-4776-87c9-e6a36221ffa9
-- title:
--   Proposition 5, p. 26 — at α = 1/2, neutrality is moot for r > ρ_L/ρ_H; for r < ρ_L/ρ_H it lowers consumer surplus, raises π_T, and raises π_F when ρ_H, ρ_L are large
-- statement:
--   Fix equal popularity $\alpha=1/2$. Compare the market without search neutrality (sellers price in $[0,1]$, then the platform ranks optimally for each consumer type) with the market with search neutrality ($F$ prominent for type $f$, $T$ prominent for type $t$).
--
--   1. **High commission.** If $0<\rho_L<\rho_H<1$ and $\rho_L/\rho_H<r<1$, search neutrality does not affect the equilibrium outcome: for every equilibrium $(p_F,p_T,\sigma)$ without neutrality and every equilibrium $(q_F,q_T)$ with neutrality, $p_F=q_F$, $p_T=q_T$, the platform ranks neutrally at $(p_F,p_T)$, and the platform's profit, the third-party seller's profit and the consumer surplus coincide.
--   2. **Low commission.** If $0<\rho_L<\rho_H<1$ and $0\le r<\rho_L/\rho_H$, then for every such pair of equilibria
--   $$CS^{S}<CS^{NS}\qquad\text{and}\qquad \pi_T^{NS}<\pi_T^{S}.$$
--   3. **Platform profit.** There is a threshold $\bar\rho<1$ such that whenever $\bar\rho<\rho_L<\rho_H<1$ and $0\le r<\rho_L/\rho_H$, every pair of equilibria satisfies $\pi_F^{NS}<\pi_F^{S}$.
--
--   Search neutrality only matters when the commission is low enough for the platform to self-preference; then it softens price competition, which hurts consumers and helps the third-party seller, and when consumers' match probabilities are high it helps the platform too.
--
--   **Formalization Note**
--   - "Does not affect the equilibrium outcome" is read as equal prices, rankings, both profits and consumer surplus. It is stated for $r>\rho_L/\rho_H$: at $r=\rho_L/\rho_H$ the platform is indifferent for type-$t$ consumers at $(1,1)$, and a ranking rule breaking that tie toward $F$ supports a second, different equilibrium.
--   - "Reduces" and "improves" are read strictly; "sufficiently large" is read as one threshold $\bar\rho<1$ that does not depend on $r$.
--   - The comparisons are over every equilibrium with and every equilibrium without neutrality. They are not vacuous: existence is part of the milestones Lemma 1 and Proposition 4(1)–(2).
--   - With neutrality and $(p_F,p_T)=(1,1)$ consumer surplus is $0$, since no consumer pays less than her value.
--   - $0\le r<1$ is a disclosed reading of "percentage commission"; at $r=1$ the third party is indifferent among all prices.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), p. 26, Proposition 5

import Mathlib
import Definitions.Def_SearchNeutrality_Commission_Model

namespace SearchNeutrality.Commission

/-- Proposition 5, p. 26: at `α = 1/2`, (a) for `r > ρ_L/ρ_H` search neutrality does not affect
the equilibrium outcome; (b) for `r < ρ_L/ρ_H` it strictly reduces consumer surplus and strictly
raises the third-party seller's profit; (c) there is `ρ̄ < 1` such that for `ρ̄ < ρ_L < ρ_H < 1`
and every `r < ρ_L/ρ_H` it strictly raises the platform's profit. -/
theorem proposition_5 :
    (∀ ρH ρL r : ℝ, 0 < ρL → ρL < ρH → ρH < 1 → 0 ≤ r → r < 1 →
      (ρL / ρH < r →
        ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ →
        ∀ qF qT : ℝ, IsSEquilibrium ρH ρL r (1 / 2) qF qT →
          pF = qF ∧ pT = qT ∧ σ pF pT = neutral ∧
          platformProfit ρH ρL r (1 / 2) (σ pF pT) pF pT
            = platformProfit ρH ρL r (1 / 2) neutral qF qT ∧
          sellerProfit ρH ρL r (1 / 2) (σ pF pT) pF pT
            = sellerProfit ρH ρL r (1 / 2) neutral qF qT ∧
          consumerSurplus ρH ρL (1 / 2) (σ pF pT) pF pT
            = consumerSurplus ρH ρL (1 / 2) neutral qF qT) ∧
      (r < ρL / ρH →
        ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ →
        ∀ qF qT : ℝ, IsSEquilibrium ρH ρL r (1 / 2) qF qT →
          consumerSurplus ρH ρL (1 / 2) neutral qF qT
            < consumerSurplus ρH ρL (1 / 2) (σ pF pT) pF pT ∧
          sellerProfit ρH ρL r (1 / 2) (σ pF pT) pF pT
            < sellerProfit ρH ρL r (1 / 2) neutral qF qT)) ∧
    (∃ ρbar : ℝ, ρbar < 1 ∧
      ∀ ρH ρL r : ℝ, 0 < ρL → ρbar < ρL → ρL < ρH → ρH < 1 → 0 ≤ r → r < ρL / ρH →
        ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ →
        ∀ qF qT : ℝ, IsSEquilibrium ρH ρL r (1 / 2) qF qT →
          platformProfit ρH ρL r (1 / 2) (σ pF pT) pF pT
            < platformProfit ρH ρL r (1 / 2) neutral qF qT) := by sorry

end SearchNeutrality.Commission
