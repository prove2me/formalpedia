-- Prove2me | Theorems.Thm_QuantumEcon_Duopoly_proposition_2
-- name    : QuantumEcon.Duopoly.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:17.255863+00:00
-- url     : https://prove2.me/theorems/a57e03ca-c15d-4156-9d60-8bdc381e707d
-- title:
--   Proposition 2: more quantum investment despite higher scaling cost
-- statement:
--   There are parameters satisfying the paper’s standing and Lemma 1 assumptions with $B_2<B_1$ for which a subgame-perfect equilibrium exists and every such equilibrium has $x_2<x_1$. Thus the quantum firm can invest more in market creation even when its quadratic investment cost coefficient is larger.
--
--   This statement is a source-indexed target for the two-stage model.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 14, Proposition 2; PDF pp. 27–28, proof

import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false

namespace QuantumEcon.Duopoly

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF p. 14, Proposition 2; proof PDF pp. 27–28.
Formalization Note: investments and quantities are nonnegative. The exhibited instance
is `a = 20`, `c = 2`, `γ = 1`, `B₁ = 10`, `B₂ = 8`. Firm 1 is quantum. -/
theorem proposition_2 :
    ∃ P : Params, Standing P ∧ Lemma1Cond P ∧ P.B₂ < P.B₁ ∧
      (∃ x₁ x₂ : ℝ, ∃ σ : ℝ → ℝ → ℝ × ℝ, IsSPE P x₁ x₂ σ) ∧
      ∀ x₁ x₂ : ℝ, ∀ σ : ℝ → ℝ → ℝ × ℝ,
        IsSPE P x₁ x₂ σ → x₂ < x₁ := by sorry

end QuantumEcon.Duopoly
