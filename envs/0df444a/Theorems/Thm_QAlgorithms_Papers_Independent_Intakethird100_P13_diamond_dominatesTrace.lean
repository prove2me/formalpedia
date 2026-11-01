-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_diamond_dominatesTrace
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.diamond_dominatesTrace
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:01:42.693711+00:00
-- url     : https://prove2.me/theorems/af1233dc-903a-43b4-8f21-31ed2f7017d6
-- title:
--   Diamond distance dominates unassisted channel trace distance
-- statement:
--   Let $E_1,E_2$ be trace-preserving completely positive maps from a qubit to a qubit. Define the unassisted distance by the supremum of $\|E_1(\rho)-E_2(\rho)\|_1$ over normalized qubit density matrices. Define the diamond distance by the same supremum after applying $\mathrm{id}_2\otimes E_i$ to normalized two-qubit density matrices. Then
--
--   $$\|E_1-E_2\|_\diamond\ge\|E_1-E_2\|_1.$$
--
--   Both norms are full trace norms, without a factor of one half. This compares assisted and unassisted channel distinguishability.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 14, Lemma 25

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF pp.9,14, Lemma 25: two actual qubit channels,
normalized density inputs and the full trace norm on both sides. -/
theorem diamond_dominatesTrace (E F : QubitMap) (hE : IsChannel E) (hF : IsChannel F) :
    channelTraceDistance E F ≤ channelDiamondDistance E F := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
