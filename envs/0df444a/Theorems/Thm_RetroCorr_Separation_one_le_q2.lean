-- Prove2me | Theorems.Thm_RetroCorr_Separation_one_le_q2
-- name    : RetroCorr.Separation.one_le_q2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:36.235008+00:00
-- url     : https://prove2.me/theorems/1726099b-976c-43b5-b706-376350f19205
-- title:
--   §3, p. 3, first bullet — R_{2,2} transmits a faithful qubit with two-way communication: Q₂(R_{2,2}) ≥ 1
-- statement:
--   Let $S=R_{2,2}$ be the standard retrocorrectable channel with qubit control and qubit data and its Haar-distributed classical flag. Its quantum capacity assisted by two-way classical communication is at least one qubit per channel use:
--   $$Q_2(R_{2,2})\ \ge\ 1 .$$
--
--   This is the first bullet of §3: the channel "can be used to transmit a faithful qubit in the presence of two-way communication". Together with eq. (1) it gives the separation $Q_2(R_{2,2})>C_H(R_{2,2})$.
--
--   **Formalization Note** `twoWayQuantumCapacity (flagLaw 2 2) (retroBranch 2 2)` is the operational capacity of `RetroCorr.Separation.TwoWay`, a supremum in `ℝ≥0∞` of achievable rates.
--
--   Differences from the source:
--   - reading: "R_{2,2} can be used to transmit a faithful qubit in the presence of two-way communication" → 1 ≤ Q₂(R_{2,2}) in qubits per use; reason: one faithful qubit per use of the channel is the rate-1 statement, as the abstract's comparison of Q₂ with C_H requires
--   - encoding: Q₂ → supremum of achievable rates in ℝ≥0∞; reason: the capacity may a priori be infinite
--   - encoding: Q₂, defined operationally but not formally on the page → protocols with finite-dimensional memories, finite-outcome complete Kraus instruments, exactly n channel uses, Bob's memory starting one-dimensional, and worst-case pure-state fidelity ≥ 1 − η for every large n with m ≥ R n; reason: the standard operational model; a narrower protocol class can only lower Q₂, so the lower bound on Q₂ is not weakened
-- source:
--   Bennett, Devetak, Shor & Smolin, Inequalities and separations among assisted capacities of quantum channels, arXiv:quant-ph/0406086v1, p. 3, §3, first bullet

import Mathlib
import Definitions.Def_RetroCorr_Separation_Channel
import Definitions.Def_RetroCorr_Separation_TwoWay

namespace RetroCorr.Separation
theorem one_le_q2 :
    1 ≤ twoWayQuantumCapacity (flagLaw 2 2) (retroBranch 2 2) := by sorry
end RetroCorr.Separation
