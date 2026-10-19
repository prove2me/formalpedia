-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_three_cnot_eq_swap
-- name    : QAlgorithms.Nannicini.three_cnot_eq_swap
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:52:19.744614+00:00
-- url     : https://prove2.me/theorems/358ba560-dd72-4f3b-811d-2eeab2cc23d4
-- title:
--   Three CX gates implement SWAP
-- statement:
--   Let $CX_{12}$ be the controlled-NOT gate with control qubit 1 and target qubit 2, $CX_{12}|x\rangle|y\rangle=|x\rangle|y\oplus x\rangle$, and let $CX_{21}$ be the controlled-NOT gate with control qubit 2 and target qubit 1, $CX_{21}|x\rangle|y\rangle=|x\oplus y\rangle|y\rangle$. Let SWAP be the $4\times4$ permutation matrix that exchanges $|01\rangle$ and $|10\rangle$ and fixes $|00\rangle$ and $|11\rangle$. Then the circuit of Fig. 1.13 equals SWAP:
--
--   $$
--   CX_{12}\,CX_{21}\,CX_{12}=\mathrm{SWAP}.
--   $$
--
--   So a swap of two qubits can be built from three CX gates. On hardware where two-qubit gates act only on adjacent qubits, this lets any two qubits interact.
--
--   **Formalization Note** The identity is stated as an equality of $4\times4$ matrices indexed by $\{0,1\}^2$, first factor = qubit 1. $CX_{21}$ is $CX_{12}$ with both qubit indices exchanged.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 27, Proposition 1.41. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms


/-- Nannicini, Proposition 1.41, PDF p. 27. The circuit of Fig. 1.13, made of three CX gates,
`CX₁₂ CX₂₁ CX₁₂`, swaps qubits 1 and 2: it equals the SWAP matrix of p. 27.

`cnot` is `CX₁₂` (control qubit 1, target qubit 2: `|x⟩|y⟩ ↦ |x⟩|y ⊕ x⟩`, p. 26);
`cnot.submatrix Prod.swap Prod.swap` is `CX₂₁` (control qubit 2, target qubit 1); `swapGate`
is the permutation matrix exchanging `|01⟩` and `|10⟩`. -/
theorem three_cnot_eq_swap :
    cnot * cnot.submatrix Prod.swap Prod.swap * cnot = swapGate := by
  sorry



end QAlgorithms.Nannicini
