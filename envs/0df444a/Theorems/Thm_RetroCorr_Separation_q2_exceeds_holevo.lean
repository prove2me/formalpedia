-- Prove2me | Theorems.Thm_RetroCorr_Separation_q2_exceeds_holevo
-- name    : RetroCorr.Separation.q2_exceeds_holevo
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:41.531809+00:00
-- url     : https://prove2.me/theorems/86121560-0991-4b3e-95c0-782afb9cd2d0
-- title:
--   Abstract, p. 1 — the retrocorrectable channel R_{2,2} has two-way-assisted quantum capacity Q₂ exceeding its one-shot Holevo capacity C_H
-- statement:
--   Let $S=R_{2,2}$ be the standard retrocorrectable channel of Fig. 1 with a qubit control input, a qubit data input, and the classical control output $k=(B,U_1,U_2)$ consisting of a Haar-random basis $B$ of $\mathbb C^2$ and independent Haar-random unitaries $U_1,U_2$; the channel measures the control in $B$, applies $U_j$ to the data for the outcome $j$, and keeps $j$ hidden. Then its quantum capacity assisted by two-way classical communication strictly exceeds its unassisted one-shot Holevo capacity:
--   $$C_H(R_{2,2})\ <\ Q_2(R_{2,2}).$$
--
--   Here $C_H$ is the supremum over all finite input ensembles of the Holevo quantity of the full output (flag and data), in bits, and $Q_2$ is the operational capacity in qubits per use with free two-way classical communication and no prior entanglement. This is the paper's headline: a channel whose capacity for quantum information with classical assistance exceeds its capacity for unassisted classical information in a single use.
--
--   **Formalization Note** Both sides are in `ℝ≥0∞`: `holevoCapacity (flagLaw 2 2) (retroBranch 2 2)` (`RetroCorr.Separation.Holevo`) and `twoWayQuantumCapacity (flagLaw 2 2) (retroBranch 2 2)` (`RetroCorr.Separation.TwoWay`).
--
--   Differences from the source:
--   - reading: "We exhibit discrete memoryless quantum channels whose … Q₂ exceeds … C_H" → the inequality for the paper's witness S = R_{2,2}; reason: §§2–3 exhibit R_{2,2} as the channel, and the statement for it implies the existential
--   - reading: "random basis B", "random unitaries" → independent Haar laws; reason: the caption names no distribution, and Haar is the reading under which eq. (1) holds
--   - encoding: C_H and Q₂ → suprema in ℝ≥0∞ (Holevo quantity averaged over the input-independent flag; operational two-way capacity with public flags and outcomes); reason: same quantities, and no truncation of unbounded suprema
--   - encoding: basis B → a Haar unitary W whose columns are B, column phases revealed; reason: the phases are independent of the input and change no capacity
--   - encoding: Q₂, defined operationally but not formally on the page → protocols with finite-dimensional memories, finite-outcome complete Kraus instruments, exactly n channel uses, Bob's memory starting one-dimensional, and worst-case pure-state fidelity ≥ 1 − η for every large n with m ≥ R n; reason: the standard operational model; a narrower protocol class can only lower Q₂, so the lower bound on Q₂ is not weakened
-- source:
--   Bennett, Devetak, Shor & Smolin, Inequalities and separations among assisted capacities of quantum channels, arXiv:quant-ph/0406086v1, p. 1, Abstract; instantiated p. 2, eq. (1), and p. 3, Fig. 2 and §3 first bullet

import Mathlib
import Definitions.Def_RetroCorr_Separation_Channel
import Definitions.Def_RetroCorr_Separation_Holevo
import Definitions.Def_RetroCorr_Separation_TwoWay

namespace RetroCorr.Separation
theorem q2_exceeds_holevo :
    holevoCapacity (flagLaw 2 2) (retroBranch 2 2) <
      twoWayQuantumCapacity (flagLaw 2 2) (retroBranch 2 2) := by sorry
end RetroCorr.Separation
