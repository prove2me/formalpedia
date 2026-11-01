-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_two_qubit_three_cnot
-- name    : ShendeQSD.Synthesis.two_qubit_three_cnot
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:38.92089+00:00
-- url     : https://prove2.me/theorems/c495aed4-f0cf-435d-bb19-152386b5a39a
-- title:
--   §5.3: $c_2=3$, every two-qubit operator with three CNOTs, and three are needed
-- statement:
--   1. Every unitary $U$ on two qubits is implemented exactly by a circuit of one-qubit gates and CNOTs containing at most three CNOTs.
--   2. Three is optimal: some unitary on two qubits is implemented by no such circuit with fewer than three CNOTs.
--
--   The paper takes this from [27, 34, 33] as the base case $\ell=2$, $c_\ell=3$ of the recursion (18); with it, Eq. (18) gives $\tfrac9{16}4^n-\tfrac32 2^n$, and the lower bound $3$ for $n=2$ is the entry of Table 1 from [27].
--
--   **Formalization Note** Exact operator equality, no global phase, no ancilla.
--
--   Differences from the source:
--   - reading: c_2 = 3, with c_j the least number of CNOTs needed by a known algorithm → both the upper bound (every two-qubit unitary with at most 3 CNOTs) and the matching lower bound (some two-qubit unitary needs 3); reason: the stronger reading of "= 3"; Table 1 lists 3 as the lower bound for n = 2
--   - encoding: implementing an operator → circuit operator equal to U, no global phase, no ancilla; reason: one-qubit gates range over all of U(2)
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, §5.3, p. 15 (cited from [27, 34, 33]) and Table 1, p. 14

import Definitions.Def_ShendeQSD_Synthesis_cnotCount

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **§5.3: every two-qubit operator needs at most three CNOTs (`c₂ = 3`, cited from
[27, 34, 33]).**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
§5.3, p. 15: "We have recorded in Table 1 the formula for c_n with recursion bottoms out at
one-qubit operators (l = 1 and c_l = 0), or two-qubit operators (l = 2 and c_l = 3 by
[27, 34, 33])."

1. Every unitary `U` on two qubits is implemented exactly by a circuit of one-qubit gates and
   CNOTs with at most three CNOTs.
2. Three is needed: some unitary on two qubits is implemented by no such circuit with fewer than
   three CNOTs (Table 1, p. 14, lower bound 3 for `n = 2`, from [27]).

**Formalization Note.** Reading: `c₂ = 3` is read as both halves, the upper bound used by
Eq. (18) and the matching lower bound, so that `3` is the exact optimum. Exact operator equality,
no global phase, no ancilla. -/
theorem two_qubit_three_cnot :
    (∀ U ∈ Matrix.unitaryGroup (Qubits 2) ℂ,
      ∃ c : Circuit gateLib 2, c.unitary = U ∧ cnotCount c ≤ 3) ∧
    (∃ U ∈ Matrix.unitaryGroup (Qubits 2) ℂ,
      ∀ c : Circuit gateLib 2, c.unitary = U → 3 ≤ cnotCount c) := by sorry

end ShendeQSD.Synthesis
