-- Prove2me | Theorems.Thm_ReactiveCapacity_proposition_1
-- name    : ReactiveCapacity.proposition_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:19:12.108683+00:00
-- url     : https://prove2.me/theorems/3f253d1d-7095-40d2-8f0b-77b7781536d1
-- title:
--   Proposition 1: equilibrium quality, wholesale and retail prices first rise, then fall in the reactive capacity (corrected: domain Focus + HighOnlyDominated)
-- statement:
--   Let the parameters satisfy the standing assumptions, the focus condition and high-only dominance (the domain). Then:
--
--   1. **Existence.** For every reactive capacity $\bar Q\ge 0$ an equilibrium exists.
--   2. **Shape.** There is $\bar Q'<1$ such that for $\bar Q_1<\bar Q_2$ and equilibrium outcomes $e_1$ at $\bar Q_1$ and $e_2$ at $\bar Q_2$:
--      - if $0\le\bar Q_1$ and $\bar Q_2\le\bar Q'$, then $q^*(e_1)\le q^*(e_2)$, $w^*(e_1)\le w^*(e_2)$ and $p^*(e_1)\le p^*(e_2)$ in each market state;
--      - if $\bar Q'<\bar Q_1$, then $q^*(e_1)\ge q^*(e_2)$, $w^*(e_1)\ge w^*(e_2)$ and $p^*(e_1)\ge p^*(e_2)$ in each market state.
--   3. **Non-monotonicity.** The parameters $(\theta_H,\theta_L,\alpha_g,\alpha_b,\rho,k)=(3,1,1/2,1/100,1/10,1)$ lie in the domain, and for all equilibrium outcomes at $\bar Q=0$, $2/5$ and $1/2$,
--   $$
--   q^*(0)<q^*(2/5)>q^*(1/2),\qquad w^*(0)<w^*(2/5)>w^*(1/2),\qquad p^*(0)<p^*(2/5)>p^*(1/2)\ \text{in each state}.
--   $$
--
--   A higher reactive capacity first lowers the wholesale premium the retailer must pay to induce pre-season inventory, which raises its margin and its incentive to invest in quality; beyond $\bar Q'$ it mainly lets the retailer serve all consumers in the bad market, which lowers the average valuation of the consumers it targets and therefore the quality it chooses.
--
--   **Formalization Note** Equilibria are the subgame-perfect equilibria of the game of p.13, not the paper's tables. At the instance the values are $q^*=189/380,\ 24/43,\ 21/38$ and $w^*\approx 0.2749,\ 0.3115,\ 0.3054$.
--
--   Differences from the source:
--   - correction: all parameters with $\alpha_b<\theta_L/\theta_H<\alpha_g$ and footnote 1 → the domain Focus ∧ HighOnlyDominated; reason: at $(4,1,19/20,1/50,1/10,1)$, which satisfies all of the paper's assumptions, $q^*(0)=0.65$, $q^*(1/2)\approx 0.6432$ and $q^*(1)=2$ in the game, so no $\bar Q'$ exists.
--   - reading: footnote 4's assumption $\alpha_g\le(\theta_H/\theta_L)\alpha_b$ "for the presented analysis" (p.14) → its other case $\alpha_g>(\theta_H/\theta_L)\alpha_b$, implied by Focus; reason: with footnote 1 required for every $\bar Q\ge 0$ the first case is unsatisfiable (footnote 1's right side $\to 0$ as $\bar Q\downarrow(\theta_H/\theta_L)\alpha_b-\alpha_g$), and footnote 4 says the results "hold qualitatively the same" in the second.
--   - reading: "can have a non-monotonic effect" → both the threshold shape for every parameter in the domain (clause 2) and strict non-monotonicity at an explicit instance (clause 3); reason: neither reading of "can" is dropped.
--   - reading: "Similarly, $\bar Q$ can also have non-monotonic effects on $w^*$ and $p^*$" → the same $\bar Q'$ and the same shape for $w^*$, and for $p^*$ in each market state; reason: the paper states no separate threshold, and its tables give this one.
--   - generalization: the comparative statics of "the" equilibrium → existence for every $\bar Q\ge 0$ (clause 1), and clause 2 for every pair of equilibrium outcomes; reason: it specializes to the paper's claim wherever the equilibrium is unique.
--   - encoding: the contracts with $\varepsilon\to 0$ and the separate accept/reject decision → subgame-perfect equilibria with no $\varepsilon$, rejection being $I=0$; reason: the paper sets $\varepsilon=0$ in the results (OA p.7, fn 3), and rejecting is producing nothing.
-- source:
--   Jiang–Tian, Effects of Reactive Capacity, SSRN 3308215 (version of May 5, 2022), Proposition 1, p.20 (PDF 20)

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game
import Definitions.Def_ReactiveCapacity_ClosedForms

namespace ReactiveCapacity

/-- Proposition 1: reactive capacity has a non-monotonic effect on quality, the wholesale price and
the retail price. Jiang–Tian, *Effects of Reactive Capacity*, SSRN 3308215 (version of May 5, 2022),
Proposition 1, p.20 (PDF 20).

1. Existence: on `Dom`, an equilibrium exists for every `Q̄ ≥ 0`.
2. Shape: on `Dom`, there is `Q̄' < 1` such that for `Q̄₁ < Q̄₂` and equilibrium outcomes
   `e₁` at `Q̄₁`, `e₂` at `Q̄₂`: if `0 ≤ Q̄₁` and `Q̄₂ ≤ Q̄'` then `q*`, `w*` and `p*` (in each market
   state) weakly increase from `e₁` to `e₂`; if `Q̄' < Q̄₁` they weakly decrease.
3. Non-monotone at an instance: `P₀ = (θ_H, θ_L, α_g, α_b, ρ, k) = (3, 1, 1/2, 1/100, 1/10, 1)` lies in
   `Dom`, and for all equilibrium outcomes at `Q̄ = 0`, `2/5`, `1/2`, each of `q*`, `w*` and `p*`
   (in each state) is strictly larger at `2/5` than at `0` and at `1/2`.

**Formalization Note** The statement is on the corrected domain `Dom = Standing ∧ Focus ∧
HighOnlyDominated`; the printed claim fails on the paper's stated domain. Equilibria are the
subgame-perfect equilibria of the game of p.13 (`IsSPE`), not the printed tables. -/
theorem proposition_1 :
    (∀ P : Params, P.Dom → ∀ Qbar : ℝ, 0 ≤ Qbar → ∃ e : Outcome, IsEquilibrium P Qbar e) ∧
    (∀ P : Params, P.Dom → ∃ Q' : ℝ, Q' < 1 ∧
      ∀ Q₁ Q₂ : ℝ, ∀ e₁ e₂ : Outcome, Q₁ < Q₂ → IsEquilibrium P Q₁ e₁ → IsEquilibrium P Q₂ e₂ →
        (0 ≤ Q₁ → Q₂ ≤ Q' → e₁.q ≤ e₂.q ∧ e₁.w ≤ e₂.w ∧ ∀ s : State, e₁.p s ≤ e₂.p s) ∧
        (Q' < Q₁ → e₂.q ≤ e₁.q ∧ e₂.w ≤ e₁.w ∧ ∀ s : State, e₂.p s ≤ e₁.p s)) ∧
    ((⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ : Params).Dom ∧
      ∀ e₀ e₁ e₂ : Outcome, IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ 0 e₀ →
        IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ (2 / 5) e₁ →
        IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ (1 / 2) e₂ →
        e₀.q < e₁.q ∧ e₂.q < e₁.q ∧ e₀.w < e₁.w ∧ e₂.w < e₁.w ∧
        ∀ s : State, e₀.p s < e₁.p s ∧ e₂.p s < e₁.p s) := by sorry

end ReactiveCapacity
