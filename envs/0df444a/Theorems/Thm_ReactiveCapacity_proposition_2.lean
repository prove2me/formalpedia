-- Prove2me | Theorems.Thm_ReactiveCapacity_proposition_2
-- name    : ReactiveCapacity.proposition_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:19:14.809559+00:00
-- url     : https://prove2.me/theorems/b68429e5-919e-4d07-9eca-04a3d9ac70f5
-- title:
--   Proposition 2: more reactive capacity makes the retailer better off and can make the supplier worse off
-- statement:
--   Under the standing assumptions and the focus condition (footnote 1 of the Online Appendix):
--
--   1. the retailer's equilibrium profit weakly increases in the reactive capacity: for $0\le\bar Q_1<\bar Q_2$ and equilibrium outcomes $e_1$ at $\bar Q_1$ and $e_2$ at $\bar Q_2$,
--   $$
--   \pi_R(e_1)\le\pi_R(e_2);
--   $$
--   2. there is a $\bar Q''$ with
--   $$
--   \frac{\theta_H}{\theta_L}\alpha_b-\alpha_g<\bar Q''<1-\alpha_g
--   $$
--   such that the supplier's equilibrium profit weakly decreases in $\bar Q$ when $\bar Q\ge\bar Q''$: $\pi_S(e_2)\le\pi_S(e_1)$ whenever $\bar Q''\le\bar Q_1<\bar Q_2$;
--   3. the supplier can become worse off: the parameters $(\theta_H,\theta_L,\alpha_g,\alpha_b,\rho,k)=(3,1,1/2,1/100,1/10,1)$ satisfy the standing assumptions, the focus condition and high-only dominance, equilibria exist at $\bar Q=0$ and $\bar Q=2/5$, and for all of them
--   $$
--   \pi_S(2/5)=0<\pi_S(0),\qquad \pi_R(0)<\pi_R(2/5).
--   $$
--
--   Better reactive capacity lowers the supplier's inventory risk, but it also lets the retailer cut the wholesale price it must pay to induce inventory; beyond $\bar Q''$ the second effect dominates.
--
--   **Formalization Note** Equilibria are the subgame-perfect equilibria of the game of p.13, and the statement is about every equilibrium outcome. Clauses 1 and 2 are on the paper's own assumptions, not on the smaller domain of Proposition 1.
--
--   Differences from the source:
--   - reading: "the supplier can become worse off" → clause 2 for every parameter, and in addition the strict drop of $\pi_S$ together with the strict rise of $\pi_R$ at an explicit instance (clause 3); reason: "can" is read both as the threshold statement the paper calls "mathematically" and as a witnessed instance, so neither reading is dropped.
--   - reading: the paper's assumptions for a statement across all ranges of $\bar Q$ → $\alpha_b<\theta_L/\theta_H<\alpha_g$ with footnote 1 for every $\bar Q\ge 0$ (the focus condition); reason: footnote 1 is required in each range, which forces the second case of footnote 4 ($\alpha_g>(\theta_H/\theta_L)\alpha_b$), where the paper says its results hold "qualitatively the same".
-- source:
--   Jiang–Tian, Effects of Reactive Capacity, SSRN 3308215 (version of May 5, 2022), Proposition 2, p.22 (PDF 22)

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game
import Definitions.Def_ReactiveCapacity_ClosedForms

namespace ReactiveCapacity

/-- Proposition 2: more reactive capacity helps the retailer and can hurt the supplier. Jiang–Tian,
*Effects of Reactive Capacity*, SSRN 3308215 (version of May 5, 2022), Proposition 2, p.22
(PDF 22).

1. On the paper's domain (`Standing` and footnote 1, i.e. `Focus`), `π*_R` weakly increases in `Q̄ ≥ 0`: for `0 ≤ Q̄₁ < Q̄₂` and equilibrium outcomes `e₁`
   at `Q̄₁` and `e₂` at `Q̄₂`, `π_R(e₁) ≤ π_R(e₂)`.
2. On the same domain, there is `Q̄'' ∈ ((θ_H/θ_L)α_b − α_g, 1 − α_g)` such that `π*_S` weakly
   decreases in `Q̄` when `Q̄ ≥ Q̄''`.
3. The supplier can become worse off: at `P₀ = (θ_H, θ_L, α_g, α_b, ρ, k) = (3, 1, 1/2, 1/100, 1/10, 1)`,
   which lies in `Dom`, equilibria exist at `Q̄ = 0` and `Q̄ = 2/5`, and for all of them
   `π*_S(2/5) = 0 < π*_S(0)` while `π*_R(0) < π*_R(2/5)`.

**Formalization Note** Equilibria are the subgame-perfect equilibria of the game of p.13
(`IsSPE`). Clauses 1–2 are on `Standing ∧ Focus`, the paper's own assumptions (footnote 1 of the
Online Appendix for every `Q̄`), not on the smaller `Dom` of Proposition 1: no counterexample to
Proposition 2 on that domain is known. There is no equilibrium at `Q̄ < 0`. -/
theorem proposition_2 :
    (∀ P : Params, P.Standing → P.Focus → ∀ Q₁ Q₂ : ℝ, ∀ e₁ e₂ : Outcome, 0 ≤ Q₁ → Q₁ < Q₂ →
      IsEquilibrium P Q₁ e₁ → IsEquilibrium P Q₂ e₂ → e₁.πR ≤ e₂.πR) ∧
    (∀ P : Params, P.Standing → P.Focus → ∃ Q'' : ℝ, P.θH / P.θL * P.αb - P.αg < Q'' ∧ Q'' < 1 - P.αg ∧
      ∀ Q₁ Q₂ : ℝ, ∀ e₁ e₂ : Outcome, Q'' ≤ Q₁ → Q₁ < Q₂ →
        IsEquilibrium P Q₁ e₁ → IsEquilibrium P Q₂ e₂ → e₂.πS ≤ e₁.πS) ∧
    ((⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ : Params).Dom ∧
      (∃ e : Outcome, IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ 0 e) ∧
      (∃ e : Outcome, IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ (2 / 5) e) ∧
      ∀ e₀ e₁ : Outcome, IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ 0 e₀ →
        IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ (2 / 5) e₁ →
        e₁.πS = 0 ∧ 0 < e₀.πS ∧ e₀.πR < e₁.πR) := by sorry

end ReactiveCapacity
