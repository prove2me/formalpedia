-- Prove2me | Theorems.Thm_QuantumEcon_Duopoly_optimal_profits
-- name    : QuantumEcon.Duopoly.optimal_profits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:41:52.421792+00:00
-- url     : https://prove2.me/theorems/85db63cc-f4be-4ad2-912b-b20e1c33c076
-- title:
--   Optimal profit functions after (5)–(6)
-- statement:
--   Under the standing and Lemma 1 assumptions, each firm’s profit at every subgame-perfect equilibrium equals its explicit optimal-profit formula displayed after equations (5)–(6). The two formulas record the equilibrium payoffs.
--
--   This statement is a source-indexed target for the two-stage model.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 12, display following (5)–(6)

import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false

namespace QuantumEcon.Duopoly

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF p. 12, optimal profit display after (5)–(6).
Formalization Note: profits are evaluated at every subgame-perfect equilibrium. -/
theorem optimal_profits (P : Params) (hP : Standing P) (hL : Lemma1Cond P)
    (x₁ x₂ : ℝ) (σ : ℝ → ℝ → ℝ × ℝ) (hσ : IsSPE P x₁ x₂ σ) :
    profit₁ P x₁ (σ x₁ x₂).1 (σ x₁ x₂).2 =
      P.B₁ * (-8 + P.B₁ * (-4 + P.γ ^ 2) ^ 2) *
        (P.a * (-4 + P.B₂ * (-2 + P.γ) ^ 2 * (2 + P.γ)) +
          P.c * (4 - P.B₂ * (-2 + P.c * P.γ) * (-4 + P.γ ^ 2))) ^ 2 /
        (Fden P) ^ 2 ∧
    profit₂ P x₂ (σ x₁ x₂).1 (σ x₁ x₂).2 =
      P.B₂ * (-8 + P.B₂ * (-4 + P.γ ^ 2) ^ 2) *
        (4 * P.c ^ 2 + P.B₁ * P.c * (2 * P.c - P.γ) * (-4 + P.γ ^ 2) +
          P.a * (-4 + P.B₁ * (-2 + P.γ) ^ 2 * (2 + P.γ))) ^ 2 /
        (Fden P) ^ 2 := by sorry

end QuantumEcon.Duopoly
