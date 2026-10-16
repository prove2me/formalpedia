-- Prove2me | Theorems.Thm_QuantumEcon_Duopoly_prop2_instance
-- name    : QuantumEcon.Duopoly.prop2_instance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:01.828+00:00
-- url     : https://prove2.me/theorems/79d2f029-880a-4549-8794-6d3aba57c67f
-- title:
--   Proof of Proposition 2: numerical witness
-- statement:
--   At $a=20$, $c=2$, $\gamma=1$, $B_1=10$, and $B_2=8$, all standing and Lemma 1 assumptions hold. The Section 7 threshold is $107/15$, and investments are $x_1^*=102/109$ and $x_2^*=89/109$. This is the witness printed in the proof.
--
--   This statement is a source-indexed target for the two-stage model.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 28, proof of Proposition 2

import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false

namespace QuantumEcon.Duopoly

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF p. 28, numerical instance in the proof of Proposition 2.
Formalization Note: firm 1 is quantum, with `B₁ = 10`; firm 2 is classical, with `B₂ = 8`. -/
theorem prop2_instance :
    let P : Params := ⟨20, 2, 1, 10, 8⟩
    Standing P ∧ Lemma1Cond P ∧ P.B₂ < P.B₁ ∧
      prop2Threshold P = 107 / 15 ∧
      xStar₁ P = 102 / 109 ∧ xStar₂ P = 89 / 109 := by sorry

end QuantumEcon.Duopoly
