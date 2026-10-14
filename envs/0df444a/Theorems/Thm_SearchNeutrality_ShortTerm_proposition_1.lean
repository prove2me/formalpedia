-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_proposition_1
-- name    : SearchNeutrality.ShortTerm.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:39:42.342324+00:00
-- url     : https://prove2.me/theorems/e41ae7ab-ec25-4168-a888-5d8a5f39be4f
-- title:
--   Proposition 1, p. 16 — without neutrality an equilibrium exists, p_F^{NS*} > p_T^{NS*}, and both prices strictly rise with α until α₁^NS, then stay at (1, 1/2)
-- statement:
--   Let $1>\rho_H>\rho_L>0$, $r\in[0,1]$, and assume Condition 1. Without search neutrality:
--
--   1. for every $\alpha\in[0,1]$ an equilibrium $(p_F,p_T,\sigma)$ exists;
--   2. in every equilibrium, at every $\alpha\in[0,1]$, the first-party price is higher: $p_F>p_T$;
--   3. for $0\le\alpha<\alpha'<\alpha_1^{NS}$, every equilibrium at $\alpha$ and every equilibrium at $\alpha'$ satisfy $p_F<p_F'$ and $p_T<p_T'$;
--   4. for $\alpha\in[\alpha_1^{NS},1]$, every equilibrium has
--   $$
--   p_F=1,\qquad p_T=\tfrac12,
--   $$
--   except at $\alpha=1$ when $\rho_L>\sqrt{2/(3-r)}$.
--
--   Here $\alpha_1^{NS}$ is the threshold of the Appendix (p. 42). The proposition describes self-preferencing in prices: product $T$ is never prominent, so its seller prices low to invite search, and the first party's price rises with its popularity until it reaches the maximal price $1$.
--
--   **Formalization Note** "Strictly increase" is a comparison between equilibria at different values of $\alpha$. The exception in item 4 corrects a boundary slip: when $\rho_L>\sqrt{2/(3-r)}$ the page sets $\alpha_1^{NS}=1$, but then the interior case applies on all of $[0,1]$ (the bracket of (A2) is negative at $\alpha=1$), and at $\alpha=1$ the equilibrium price is $p_F^{NS}<1$, not $1$. Uniqueness of the equilibrium, asserted in the sentence before the proposition, is the separate item `ns_uniqueness`. The proofs of the paper's propositions are in an online appendix that is not part of the source file.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), p. 16, Proposition 1; Appendix, p. 42 (α_{NS,1})

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model
import Definitions.Def_SearchNeutrality_ShortTerm_ClosedForms

namespace SearchNeutrality.ShortTerm

/-- Proposition 1 (p. 16): under Condition 1, without search neutrality an equilibrium exists for
every `α ∈ [0,1]`; (1) in every equilibrium `p_F > p_T`; (2) both prices strictly increase with `α`
on `[0, α_1^{NS})`, and equal `p_F = 1`, `p_T = 1/2` on `[α_1^{NS}, 1]` (at `α = 1` only when
`ρ_L ≤ √(2/(3 − r))`; see the Formalization Note). -/
theorem proposition_1 (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hC : Condition1 ρH ρL r) :
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      ∃ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r α pF pT σ) ∧
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking),
      IsNSEquilibrium ρH ρL r α pF pT σ → pT < pF) ∧
    (∀ α α' : ℝ, 0 ≤ α → α < α' → α' < alpha1NS ρH ρL r →
      ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking) (pF' pT' : ℝ) (σ' : ℝ → ℝ → Ranking),
        IsNSEquilibrium ρH ρL r α pF pT σ → IsNSEquilibrium ρH ρL r α' pF' pT' σ' →
          pF < pF' ∧ pT < pT') ∧
    (∀ α : ℝ, alpha1NS ρH ρL r ≤ α → α ≤ 1 → (α < 1 ∨ ρL ≤ Real.sqrt (2 / (3 - r))) →
      ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking),
        IsNSEquilibrium ρH ρL r α pF pT σ → pF = 1 ∧ pT = 1 / 2) := by sorry

end SearchNeutrality.ShortTerm
