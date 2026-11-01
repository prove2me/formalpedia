-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_maximalPauliDistance
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.maximalPauliDistance
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:57:44.911074+00:00
-- url     : https://prove2.me/theorems/6ae33e96-da76-43f6-ba36-67a3bd6f1077
-- title:
--   Largest attainable diamond distance from Pauli channels
-- statement:
--   Fix $0\le\gamma\le1$ and the normalized amplitude-damping Choi state $\chi_\gamma$. Every channel $E$ simulated over this resource by a conditional classical law in the Bell/Pauli protocol admits a Pauli channel $P$ satisfying
--
--   $$\|E-P\|_\diamond\le\gamma.$$
--
--   Let $E_*$ be the physical protocol that ignores Alice's classical label and always applies $I$. There is a Pauli channel $P_*$ with $\|E_*-P_*\|_\diamond=\gamma$, and every Pauli $P$ satisfies $\gamma\le\|E_*-P\|_\diamond$. Thus the largest attainable distance is achieved and equals $\gamma$, including both endpoints. All distances use the full trace norm with a normalized qubit reference.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 10, Consequence following Proposition 19

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF p.10: upper bound for every attainable channel and
attainment by always applying I; gamma=0 and gamma=1 are retained. -/
theorem maximalPauliDistance (gamma : ℝ) (h0 : 0 ≤ gamma) (h1 : gamma ≤ 1) :
    (∀ p : Fin 4 → Fin 4 → ℝ, ClassicalTeleportationLaw p →
      ∃ F : QubitMap, IsPauli F ∧
        channelDiamondDistance (noisyTeleport (normalizedQubitChoi (blochAmplitudeDamping gamma)) p) F ≤ gamma) ∧
    (∃ F : QubitMap, IsPauli F ∧
      channelDiamondDistance
        (noisyTeleport (normalizedQubitChoi (blochAmplitudeDamping gamma)) discardClassical) F = gamma) ∧
    (∀ F : QubitMap, IsPauli F → gamma ≤ channelDiamondDistance
      (noisyTeleport (normalizedQubitChoi (blochAmplitudeDamping gamma)) discardClassical) F) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
