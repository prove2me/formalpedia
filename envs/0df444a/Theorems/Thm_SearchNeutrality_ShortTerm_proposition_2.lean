-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_proposition_2
-- name    : SearchNeutrality.ShortTerm.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:39:33.456699+00:00
-- url     : https://prove2.me/theorems/9d73ef24-0f6d-4b9f-a05e-1e7aed5ddad9
-- title:
--   Proposition 2, pp. 17–18 — with neutrality a unique equilibrium exists; thresholds α₁^S ≤ α₂^S < 1/2 < α₃^S ≤ α₄^S govern the price order and the monotonicity of p_F^{S*}, p_T^{S*}
-- statement:
--   Let $1>\rho_H>\rho_L>0$, $r\in[0,1]$, and assume Condition 1. There are thresholds
--   $$
--   0\le\alpha_1\le\alpha_2<\tfrac12<\alpha_3\le\alpha_4\le1,\qquad \alpha_2=\frac{\rho_L^2(1-r\rho_H)}{\rho_H+\rho_L^2(1-r\rho_H)},\quad \alpha_3=\frac{\rho_H}{\rho_H+\rho_L^2},
--   $$
--   such that, with search neutrality:
--
--   1. for every $\alpha\in[0,1]$ an equilibrium exists, and any two equilibria at the same $\alpha$ have the same prices;
--   2. in every equilibrium at $\alpha\in[0,1]$: $p_F>p_T$ if and only if $\alpha\in(\alpha_3,1]$, and $p_F<p_T$ if and only if $\alpha\in[0,\alpha_2)$;
--   3. $p_F$ strictly increases on $[0,\alpha_2)$, equals $1$ on $[\alpha_2,\alpha_4)$ and strictly decreases on $[\alpha_4,1]$;
--   4. $p_T$ strictly increases on $[0,\alpha_1)$, equals $1$ on $[\alpha_1,\alpha_3)$ and strictly decreases on $[\alpha_3,1]$.
--
--   Under neutrality the more popular product carries the higher price, in contrast to Proposition 1, where the first-party price is always the higher one.
--
--   **Formalization Note** "Increases" and "decreases" are read strictly, as comparisons between equilibria at different values of $\alpha$; the paper's Figure 2 and closed forms are strictly monotone there. The thresholds $\alpha_1,\alpha_4$ are existential, because the page's formulas for $\alpha_1^S$ and $\alpha_4^S$ are misprinted; $\alpha_2,\alpha_3$ are pinned to the page's (correct) definitions. Existence and uniqueness come from the sentence before the proposition (p. 17).
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), pp. 17–18, Proposition 2 and the sentence before it; Appendix, p. 45 (α_2^S, α_3^S)

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model
import Definitions.Def_SearchNeutrality_ShortTerm_ClosedForms

namespace SearchNeutrality.ShortTerm

/-- Proposition 2 (pp. 17–18), with the existence and uniqueness sentence before it (p. 17):
under Condition 1 there are thresholds `0 ≤ α_1 ≤ α_2 < 1/2 < α_3 ≤ α_4 ≤ 1`, with
`α_2 = α_2^S` and `α_3 = α_3^S`, such that with search neutrality a unique equilibrium exists for
every `α ∈ [0,1]`; (1) `p_F > p_T` iff `α ∈ (α_3, 1]` and `p_F < p_T` iff `α ∈ [0, α_2)`;
(2) `p_F` strictly increases on `[0, α_2)`, equals `1` on `[α_2, α_4)` and strictly decreases on
`[α_4, 1]`; `p_T` strictly increases on `[0, α_1)`, equals `1` on `[α_1, α_3)` and strictly
decreases on `[α_3, 1]`. -/
theorem proposition_2 (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hC : Condition1 ρH ρL r) :
    ∃ α1 α2 α3 α4 : ℝ,
      0 ≤ α1 ∧ α1 ≤ α2 ∧ α2 < 1 / 2 ∧ 1 / 2 < α3 ∧ α3 ≤ α4 ∧ α4 ≤ 1 ∧
      α2 = alpha2S ρH ρL r ∧ α3 = alpha3S ρH ρL ∧
      -- existence and uniqueness
      (∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∃ pF pT : ℝ, IsSEquilibrium ρH ρL r α pF pT) ∧
      (∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∀ pF pT qF qT : ℝ,
        IsSEquilibrium ρH ρL r α pF pT → IsSEquilibrium ρH ρL r α qF qT → pF = qF ∧ pT = qT) ∧
      -- (1) price order
      (∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∀ pF pT : ℝ, IsSEquilibrium ρH ρL r α pF pT →
        ((pT < pF ↔ α3 < α) ∧ (pF < pT ↔ α < α2))) ∧
      -- (2) the pattern of p_F
      (∀ α α' : ℝ, 0 ≤ α → α < α' → α' < α2 → ∀ pF pT pF' pT' : ℝ,
        IsSEquilibrium ρH ρL r α pF pT → IsSEquilibrium ρH ρL r α' pF' pT' → pF < pF') ∧
      (∀ α : ℝ, α2 ≤ α → α < α4 → ∀ pF pT : ℝ,
        IsSEquilibrium ρH ρL r α pF pT → pF = 1) ∧
      (∀ α α' : ℝ, α4 ≤ α → α < α' → α' ≤ 1 → ∀ pF pT pF' pT' : ℝ,
        IsSEquilibrium ρH ρL r α pF pT → IsSEquilibrium ρH ρL r α' pF' pT' → pF' < pF) ∧
      -- (2) the pattern of p_T
      (∀ α α' : ℝ, 0 ≤ α → α < α' → α' < α1 → ∀ pF pT pF' pT' : ℝ,
        IsSEquilibrium ρH ρL r α pF pT → IsSEquilibrium ρH ρL r α' pF' pT' → pT < pT') ∧
      (∀ α : ℝ, α1 ≤ α → α < α3 → ∀ pF pT : ℝ,
        IsSEquilibrium ρH ρL r α pF pT → pT = 1) ∧
      (∀ α α' : ℝ, α3 ≤ α → α < α' → α' ≤ 1 → ∀ pF pT pF' pT' : ℝ,
        IsSEquilibrium ρH ρL r α pF pT → IsSEquilibrium ρH ρL r α' pF' pT' → pT' < pT) := by sorry

end SearchNeutrality.ShortTerm
