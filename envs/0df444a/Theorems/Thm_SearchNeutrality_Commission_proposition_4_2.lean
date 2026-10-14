-- Prove2me | Theorems.Thm_SearchNeutrality_Commission_proposition_4_2
-- name    : SearchNeutrality.Commission.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:38:35.966203+00:00
-- url     : https://prove2.me/theorems/0db1874d-30c6-463c-a342-6b0ca3ab326a
-- title:
--   Proposition 4(2), p. 24 — at α = 1/2 and r < ρ_L/ρ_H, F is prominent for all, p_F > p_T, prices monotone in r, ρ_H, ρ_L, and (1, 1/2) above 3 − 2/(ρ_Hρ_L)
-- statement:
--   Let $\alpha=1/2$ and consider the market without search neutrality (prices in $[0,1]$ set first, then an optimal ranking rule $\sigma$ of the platform). Throughout, $0<\rho_L<\rho_H<1$ and $0\le r<\rho_L/\rho_H$.
--
--   1. An equilibrium exists; in every equilibrium the platform makes $F$ prominent for both consumer types, and $p_F^{NS*}>p_T^{NS*}$.
--   2. If $3-\frac{2}{\rho_H\rho_L}<r$, every equilibrium has $p_F^{NS*}=1$ and $p_T^{NS*}=\tfrac12$.
--   3. On the region $r\le 3-\frac{2}{\rho_H\rho_L}$, both equilibrium prices strictly increase with $r$ and strictly decrease with $\rho_H$ and with $\rho_L$. Precisely: if two parameter points both satisfy all the conditions above together with $r\le 3-2/(\rho_H\rho_L)$, and differ only in $r$ (resp. $\rho_H$, resp. $\rho_L$), then every equilibrium at the point with the larger $r$ has strictly larger $p_F$ and $p_T$ than every equilibrium at the other point (resp. strictly smaller prices for the larger $\rho_H$, resp. $\rho_L$).
--
--   With a low commission the platform steers every consumer to its own product, and the third party must cut its price to attract search; competition is fiercer when the platform earns less on $T$ or when consumers are more likely to like $T$.
--
--   **Formalization Note** "Increase/decrease" is read strictly, and is stated as a comparison between equilibria at two parameter points, both inside the region (the comparison never crosses $r=3-2/(\rho_H\rho_L)$, beyond which prices are constant). The region is non-empty only when $\rho_H\rho_L>2/3$. "The equilibrium prices" is read as "every equilibrium". $r<1$ is implied by $r<\rho_L/\rho_H$.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), p. 24, Proposition 4(2)

import Mathlib
import Definitions.Def_SearchNeutrality_Commission_Model

namespace SearchNeutrality.Commission

/-- Proposition 4(2), p. 24: at `α = 1/2` without search neutrality and with `r < ρ_L/ρ_H`,
an equilibrium exists; in every equilibrium `F` is prominent for all consumers and
`p_T < p_F`; for `3 - 2/(ρ_H ρ_L) < r` the prices are `(1, 1/2)`; and on the region
`r ≤ 3 - 2/(ρ_H ρ_L)` both prices strictly increase with `r` and strictly decrease with `ρ_H`
and with `ρ_L`. -/
theorem proposition_4_2 :
    (∀ ρH ρL r : ℝ, 0 < ρL → ρL < ρH → ρH < 1 → 0 ≤ r → r < ρL / ρH →
      (∃ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ) ∧
      (∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ →
        σ pF pT = fPrimeAll ∧ pT < pF) ∧
      (3 - 2 / (ρH * ρL) < r →
        ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ →
          pF = 1 ∧ pT = 1 / 2)) ∧
    -- strictly increasing in `r`
    (∀ ρH ρL r r' : ℝ, 0 < ρL → ρL < ρH → ρH < 1 → 0 ≤ r → r < r' →
      r < ρL / ρH → r ≤ 3 - 2 / (ρH * ρL) → r' < ρL / ρH → r' ≤ 3 - 2 / (ρH * ρL) →
      ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking) (pF' pT' : ℝ) (σ' : ℝ → ℝ → Ranking),
        IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ → IsNSEquilibrium ρH ρL r' (1 / 2) pF' pT' σ' →
          pF < pF' ∧ pT < pT') ∧
    -- strictly decreasing in `ρ_H`
    (∀ ρH ρH' ρL r : ℝ, 0 < ρL → ρL < ρH → ρH < ρH' → ρH' < 1 → 0 ≤ r →
      r < ρL / ρH → r ≤ 3 - 2 / (ρH * ρL) → r < ρL / ρH' → r ≤ 3 - 2 / (ρH' * ρL) →
      ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking) (pF' pT' : ℝ) (σ' : ℝ → ℝ → Ranking),
        IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ → IsNSEquilibrium ρH' ρL r (1 / 2) pF' pT' σ' →
          pF' < pF ∧ pT' < pT) ∧
    -- strictly decreasing in `ρ_L`
    (∀ ρH ρL ρL' r : ℝ, 0 < ρL → ρL < ρL' → ρL' < ρH → ρH < 1 → 0 ≤ r →
      r < ρL / ρH → r ≤ 3 - 2 / (ρH * ρL) → r < ρL' / ρH → r ≤ 3 - 2 / (ρH * ρL') →
      ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking) (pF' pT' : ℝ) (σ' : ℝ → ℝ → Ranking),
        IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ → IsNSEquilibrium ρH ρL' r (1 / 2) pF' pT' σ' →
          pF' < pF ∧ pT' < pT) := by sorry

end SearchNeutrality.Commission
