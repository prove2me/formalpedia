-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_cnot_count_qsd
-- name    : ShendeQSD.Synthesis.cnot_count_qsd
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:46.469778+00:00
-- url     : https://prove2.me/theorems/d45501d3-48ce-474d-a070-bb050a2dd1fe
-- title:
--   Eq. (19): every $n$-qubit operator with at most $(23/48)\,4^n-(3/2)\,2^n+4/3$ CNOTs
-- statement:
--   Let $n\ge1$. Every unitary operator $U$ on $n$ qubits is exactly the operator of some quantum circuit built from one-qubit gates and CNOT gates (on arbitrary ordered pairs of distinct wires) that contains at most
--
--   $$
--   \frac{23}{48}\,4^n-\frac32\,2^n+\frac43
--   $$
--
--   CNOT gates.
--
--   The bound is $0$ CNOTs for one qubit, $3$ for two qubits, $20$ for three and $100$ for four (Table 1). Its leading term $\tfrac{23}{48}4^n$ is slightly below $4^n/2$, within a factor of two of the lower bound $\lceil\tfrac14(4^n-3n-1)\rceil$ of [27], and it halved the best previously published count.
--
--   **Formalization Note** The circuit's operator equals $U$ exactly, with no global phase and no ancilla qubits; one-qubit gates range over all of $U(2)$. The register is `Qubits n = Fin n → Bool` with wire $0$ the most significant qubit. The count is compared in $\mathbb R$.
--
--   Differences from the source:
--   - reading: c_n ≤ (23/48)·4^n − (3/2)·2^n + 4/3, with c_n the least number of CNOTs needed by a known synthesis algorithm (p. 14) → the existence of a circuit over the gate library implementing U with at most that many CNOTs; reason: the paper's claim (p. 3) is that an arbitrary n-qubit operator can be implemented in such a circuit
--   - encoding: implementing an operator → circuit operator equal to U, no global phase, no ancilla; reason: one-qubit gates range over all of U(2), so a global phase is absorbed; the paper's circuits use no ancilla
--   - encoding: n-qubit operators → 1 ≤ n; reason: Table 1 starts at n = 1; at n = 0 there is no wire, the operator is a phase, and no circuit can apply it
--   - encoding: bitstring states with higher wires the more significant qubits → Qubits n = Fin n → Bool, wire 0 most significant; reason: the same register; the statement quantifies over all unitaries, so the wire order changes no instance
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, Appendix A, Eq. (19), p. 16 (key result 2, p. 3; Table 1, p. 14)

import Definitions.Def_ShendeQSD_Synthesis_cnotCount

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **Eq. (19): every `n`-qubit operator with at most `(23/48)·4^n − (3/2)·2^n + 4/3` CNOTs.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
Appendix A, Eq. (19), p. 16: "This results in the following, final CNOT count.
c_n ≤ (23/48) × 4^n − (3/2) × 2^n + 4/3"; key result 2, p. 3: "An arbitrary n-qubit operator can
be implemented in a circuit containing no more than (23/48) × 4^n − (3/2) × 2^n + 4/3 CNOT gates."

For every `n ≥ 1`, every unitary `U` on `n` qubits is the operator of some circuit of one-qubit
unitary gates and CNOT gates (on any ordered pairs of distinct wires) whose number of CNOTs is at
most `(23/48)·4^n − (3/2)·2^n + 4/3`.

**Formalization Note.** Reading: `c_n ≤ …` is read as the existence of such a circuit. Encoding:
the circuit's operator equals `U` exactly (no global phase, no ancilla); the register is
`Qubits n = Fin n → Bool` with wire `0` most significant; the count is compared in `ℝ` (the bound
is `1/4` at `n = 1` and `3` at `n = 2`). -/
theorem cnot_count_qsd (n : ℕ) (hn : 1 ≤ n) (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    ∃ c : Circuit gateLib n, c.unitary = U ∧
      (cnotCount c : ℝ) ≤ 23 / 48 * 4 ^ n - 3 / 2 * 2 ^ n + 4 / 3 := by sorry

end ShendeQSD.Synthesis
