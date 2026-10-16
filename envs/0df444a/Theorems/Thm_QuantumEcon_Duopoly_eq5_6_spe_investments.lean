-- Prove2me | Theorems.Thm_QuantumEcon_Duopoly_eq5_6_spe_investments
-- name    : QuantumEcon.Duopoly.eq5_6_spe_investments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:41:52.804019+00:00
-- url     : https://prove2.me/theorems/a2f385b8-ef1e-4349-b10d-77258df71d91
-- title:
--   (5)–(6): subgame-perfect equilibrium investments
-- statement:
--   Under the standing assumptions and Lemma 1’s conditions, a subgame-perfect equilibrium exists with investments given by (5)–(6), and every subgame-perfect equilibrium has those investments and the corresponding interior Cournot quantities on the equilibrium path. This connects the paper’s closed forms to the two-stage game.
--
--   This statement is a source-indexed target for the two-stage model.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 11, (5)–(6)

import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false

namespace QuantumEcon.Duopoly

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF p. 11, (5)–(6), obtained by backward induction.
Formalization Note: equilibrium uses nonnegative investments and quantities and a
stage-2 Nash prescription at every feasible investment pair. -/
theorem eq5_6_spe_investments (P : Params) (hP : Standing P) (hL : Lemma1Cond P) :
    (∃ σ : ℝ → ℝ → ℝ × ℝ, IsSPE P (xStar₁ P) (xStar₂ P) σ) ∧
    ∀ x₁ x₂ : ℝ, ∀ σ : ℝ → ℝ → ℝ × ℝ, IsSPE P x₁ x₂ σ →
      x₁ = xStar₁ P ∧ x₂ = xStar₂ P ∧
      σ x₁ x₂ = (qStar₁ P x₁ x₂, qStar₂ P x₁ x₂) := by sorry

end QuantumEcon.Duopoly
