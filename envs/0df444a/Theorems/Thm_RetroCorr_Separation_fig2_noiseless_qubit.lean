-- Prove2me | Theorems.Thm_RetroCorr_Separation_fig2_noiseless_qubit
-- name    : RetroCorr.Separation.fig2_noiseless_qubit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:21.280542+00:00
-- url     : https://prove2.me/theorems/286fa81b-adf8-40df-982c-39b69d38f4c6
-- title:
--   Fig. 2, p. 3 — one use of S = R_{2,2} with two-way classical communication implements a noiseless qubit channel
-- statement:
--   Let $S=R_{2,2}$ be the standard retrocorrectable channel with qubit control and qubit data, with its Haar-distributed classical flag $k=(B,U_1,U_2)$. There is a two-way assisted protocol that uses $S$ exactly once, with free classical communication in both directions and no prior entanglement, and transmits one qubit without error:
--   $$\exists\ \text{two-way code }P\text{ with one use of }S\text{ for }1\text{ qubit}:\qquad \mathrm{out}_P(\rho)=\rho\quad\text{for every one-qubit density matrix }\rho .$$
--
--   In the paper's protocol, Alice feeds the control input half of an ebit and the data input the message qubit; Bob announces $B$; Alice measures the other half of the ebit in $B^T$ and, by the echo effect, obtains the channel's hidden outcome $j$, which she announces; Bob undoes $U_j$. The statement asserts that such a protocol exists in the operational model used to define $Q_2$, and that its output equals its input on every state.
--
--   **Formalization Note** `TwoWayCode (flagLaw 2 2) (retroBranch 2 2) 1 1` is a code with exactly one channel use for $m=1$ qubit (`QAlgorithms.Qubits 1`), in the adaptive model of `RetroCorr.Separation.TwoWay`; `P.output ρ` is Bob's final state. The flag is announced to both parties after the use, which is Bob telling Alice $B$ over the back channel.
--
--   Differences from the source:
--   - reading: "Protocol … to implement a noiseless qubit channel" (Fig. 2's specific protocol) → there exists a two-way code with one use of S whose output equals its input; reason: the caption's claim is that the protocol implements the identity channel, and the existence of such a code is that claim in the capacity model
--   - encoding: "noiseless qubit channel" → output = input for every one-qubit density matrix; reason: a noiseless channel is the identity on every state
--   - encoding: Bob tells Alice B; Alice tells Bob j → the flag and every instrument outcome are public; reason: free two-way classical communication
-- source:
--   Bennett, Devetak, Shor & Smolin, Inequalities and separations among assisted capacities of quantum channels, arXiv:quant-ph/0406086v1, p. 3, Fig. 2 caption

import Mathlib
import Definitions.Def_RetroCorr_Separation_Channel
import Definitions.Def_RetroCorr_Separation_TwoWay

namespace RetroCorr.Separation
theorem fig2_noiseless_qubit :
    ∃ P : TwoWayCode (flagLaw 2 2) (retroBranch 2 2) 1 1,
      ∀ ρ : Matrix (QAlgorithms.Qubits 1) (QAlgorithms.Qubits 1) ℂ,
        QAlgorithms.IsDensityMatrix ρ → P.output ρ = ρ := by sorry
end RetroCorr.Separation
