-- Prove2me | Theorems.Thm_QuantumEcon_Duopoly_proposition_1
-- name    : QuantumEcon.Duopoly.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:41:54.960418+00:00
-- url     : https://prove2.me/theorems/61ee6e6a-70f2-413e-8094-15d59b05ae8a
-- title:
--   Proposition 1: positive quantum-firm profit
-- statement:
--   For every admissible substitution parameter $\gamma\in[0,1]$ satisfying Lemma 1’s conditions, the quantum firm has strictly positive profit at every subgame-perfect equilibrium. This is the paper’s profitability claim.
--
--   This statement is a source-indexed target for the two-stage model.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 12, Proposition 1; PDF pp. 26–27, proof

import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false

namespace QuantumEcon.Duopoly

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF p. 12, Proposition 1; proof PDF pp. 26–27.
Formalization Note: `Standing` ranges over `γ ∈ [0,1]`; profit is at a genuine SPE. -/
theorem proposition_1 (P : Params) (hP : Standing P) (hL : Lemma1Cond P)
    (x₁ x₂ : ℝ) (σ : ℝ → ℝ → ℝ × ℝ) (hσ : IsSPE P x₁ x₂ σ) :
    0 < profit₁ P x₁ (σ x₁ x₂).1 (σ x₁ x₂).2 := by sorry

end QuantumEcon.Duopoly
