-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_muxRot_cnot_count
-- name    : ShendeQSD.Synthesis.muxRot_cnot_count
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:45.250271+00:00
-- url     : https://prove2.me/theorems/4c062c9d-df4f-4856-9269-05f42ba8c3db
-- title:
--   §3.2: a multiplexed rotation with $k$ select bits uses $2^k$ CNOTs
-- statement:
--   Let $R$ be $R_z$ or $R_y$ and $k\ge1$. For every assignment $\theta$ of an angle $\theta_s$ to each $s\in\{0,1\}^k$, there is a circuit on $k+1$ qubits, made of one-qubit gates and CNOTs, whose operator is exactly the multiplexed rotation
--
--   $$
--   |t\rangle|s\rangle\longmapsto\big(R(\theta_s)|t\rangle\big)|s\rangle
--   $$
--
--   (target on the top wire, selects on the $k$ wires below), and which contains exactly $2^k$ CNOT gates.
--
--   This is the per-rotation cost that enters the recursion of Eqs. (17)–(18): the three multiplexed rotations of each Quantum Shannon Decomposition step on $j$ qubits cost $3\cdot2^{j-1}$ CNOTs.
--
--   **Formalization Note** The circuit's operator equals the multiplexed rotation exactly (no global phase, no ancilla).
--
--   Differences from the source:
--   - reading: "the final CNOT count is 2^k" → a circuit with exactly 2^k CNOTs; reason: exactly is what Figure 2 builds and implies "at most"
--   - reading: k select bits → 1 ≤ k; reason: a multiplexed rotation has at least one select bit; with none the gate is a single rotation and needs no CNOT
--   - encoding: Figure 2 draws the target at the bottom → the target is wire 0, the selects are wires 1, …, k; reason: the same operator up to the order of the wires
--   - encoding: "decompose into basic gates" → circuit operator equal to the multiplexed rotation, no global phase; reason: one-qubit gates range over all of U(2)
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, §3.2, p. 11 (with Figure 2)

import Definitions.Def_ShendeQSD_Synthesis_cnotCount
import Definitions.Def_ShendeQSD_Synthesis_muxRot
import Definitions.Def_ShendeQSD_Synthesis_rz
import Definitions.Def_ShendeQSD_Synthesis_ry

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **§3.2: a multiplexed rotation with `k` select bits costs `2^k` CNOTs.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
§3.2, p. 11: "Recursive application of Theorem 8 can decompose any multiplexed rotation into basic
gates. In the process, some CNOT gates cancel, as is illustrated in Figure 2. The final CNOT count
is 2^k, for k select bits."

For `R = R_z` and `R = R_y`, every `k ≥ 1` and all angles `θ : {0,1}^k → ℝ`, some circuit of
one-qubit gates and CNOTs on `k + 1` qubits implements the multiplexed rotation `muxRotQ R θ`
exactly and contains exactly `2^k` CNOTs.

**Formalization Note.** Reading: "the final CNOT count is `2^k`" is read as exactly `2^k`.
Encoding: the target is wire `0` and the selects are wires `1, …, k` (`muxRotQ`); the paper's
Figure 2 draws the target at the bottom. Exact operator equality, no global phase. `k ≥ 1`: with
no select bit the gate is a single rotation and needs no CNOT. -/
theorem muxRot_cnot_count (R : ℝ → Matrix Bool Bool ℂ) (hR : R = rz ∨ R = ry) (k : ℕ)
    (hk : 1 ≤ k) (θ : Qubits k → ℝ) :
    ∃ c : Circuit gateLib (k + 1), c.unitary = muxRotQ R θ ∧ cnotCount c = 2 ^ k := by sorry

end ShendeQSD.Synthesis
