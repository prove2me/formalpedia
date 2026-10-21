-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_coherification
-- name    : QAlgorithms.Papers.Independent.Support21.P19.coherification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:56:34.79999+00:00
-- url     : https://prove2.me/theorems/f67e07cf-b585-47e1-9187-18989b19ebc6
-- title:
--   Proposition 1: coherification of one-way classical communication
-- statement:
--   Let $U$ be a finite-dimensional bipartite isometry (in particular, a unitary gate), let $e\in\mathbb R$ be its net entanglement budget per use, and let $C\ge0$. Alice and Bob may use free local operations and product ancillas, with every nonlocal call counted. If a sequential protocol family communicates $C$ forward classical bits per use of $U$ with vanishing worst-message error, then the same $U$ and entanglement budget permit coherent communication at the same rate:
--
--   $$
--   U+e\,[qq]\ge C\,[c\to c]\quad\Longrightarrow\quad U+e\,[qq]\ge C\,[q\to qq]\qquad(a).
--   $$
--
--   Both achievable-rate assertions allow arbitrarily small rate losses and vanishing error. The coherent conclusion retains superpositions, including arbitrary quantum references. Negative $e$ requires net generation of $-e$ EPR pairs per use. This transfers a one-way classical achievable rate to a coherent achievable rate.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 1, Proposition 1: coherification of one-way classical communication

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.1–2, Proposition 1: same U, signed entanglement budget and forward rate. -/
theorem coherification (U : Resource) (hU : IsIsometricResource U) (C e : ℝ)
    (h : AchievesTransmission U (cbitChannel 2) C e) : AchievesTransmission U (cobitChannel 2) C e := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
