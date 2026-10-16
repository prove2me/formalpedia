-- Prove2me | Theorems.Thm_QuantumEcon_Duopoly_prop2_threshold
-- name    : QuantumEcon.Duopoly.prop2_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:41:53.986221+00:00
-- url     : https://prove2.me/theorems/785c9582-8fe2-44ca-8f54-c743af0b8583
-- title:
--   Proof of Proposition 2: investment-order threshold
-- statement:
--   Under the standing assumptions and Lemma 1’s conditions, the quantum firm’s closed-form investment exceeds the classical firm’s precisely when $B_2$ exceeds the explicit threshold derived in Section 7. This gives the parameter test used by the numerical witness.
--
--   This statement is a source-indexed target for the two-stage model.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 27–28, proof of Proposition 2

import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false

namespace QuantumEcon.Duopoly

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF pp. 27–28, proof of Proposition 2: the exact investment-order
threshold under the conditions of Lemma 1. -/
theorem prop2_threshold (P : Params) (hP : Standing P) (hL : Lemma1Cond P) :
    xStar₂ P < xStar₁ P ↔ prop2Threshold P < P.B₂ := by sorry

end QuantumEcon.Duopoly
