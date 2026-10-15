-- Prove2me | Theorems.Thm_QuantumSDP18_MeasureBE_cnot_identity
-- name    : QuantumSDP18.MeasureBE.cnot_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:33.630986+00:00
-- url     : https://prove2.me/theorems/58aa5873-e5d2-45d7-b17e-31e27a3df9e7
-- title:
--   §4.1, p. 25 — with a′ = a + 1 and U′ = U ⊗ I₂, the block of U′†(I ⊗ CNOT)U′ at |0⟩^{⊗a′} equals K
-- statement:
--   Let $U$ be an operator on the system and $a$ ancilla qubits, append one fresh qubit, and put $a' = a+1$ and $U' = U\otimes I_2$. Let $\mathrm{CNOT}$ act on the measured (last) ancilla qubit as control and the fresh qubit as target. Then
--
--   $$
--   \big(I\otimes\langle 0|^{\otimes a}\big)U^\dagger(I\otimes|0\rangle\langle 0|)U\big(I\otimes|0\rangle^{\otimes a}\big)
--   = \Big(I\otimes\langle 0|^{\otimes a'}\Big)U'^\dagger(I\otimes\mathrm{CNOT})U'\Big(I\otimes|0\rangle^{\otimes a'}\Big).
--   $$
--
--   The left side is the operator $K$ whose distance from $M$ the bias controls; the right side is the top-left block of the unitary $U'^\dagger(I\otimes\mathrm{CNOT})U'$, so this identity turns a non-unitary sandwich into a block of a unitary circuit.
--
--   **Formalization Note** The page does not print the direction of the CNOT. With the measured qubit as control and the fresh qubit as target the identity holds; with the roles swapped the right side is $U^\dagger U$, so the direction is pinned to the first. No hypothesis on $U$ is needed.
-- source:
--   van Apeldoorn and Gilyén, Improvements in quantum SDP-solving with applications, arXiv:1804.05058v1, p. 25, §4.1, 'Finally let a′ := a + 1 and U′ := U ⊗ I₂, then it is easy to see that' and the display that follows

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_MeasureBE_Setting

namespace QuantumSDP18.MeasureBE

/-- §4.1, p. 25: with `a′ := a + 1` and `U′ := U ⊗ I₂`,
`(I ⊗ ⟨0|^{⊗a}) U† (I ⊗ |0⟩⟨0|) U (I ⊗ |0⟩^{⊗a}) = (I ⊗ ⟨0|^{⊗a′}) U′† (I ⊗ CNOT) U′ (I ⊗ |0⟩^{⊗a′})`,
the CNOT controlled by the measured (last) ancilla qubit and targeting the fresh qubit. -/
theorem cnot_identity {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℕ)
    (U : Matrix (ι × Anc c) (ι × Anc c) ℂ) :
    blockK c U = (ketZeroPrime (ι := ι) c).conjTranspose * (Uprime c U).conjTranspose *
      cnotLast (ι := ι) c * Uprime c U * ketZeroPrime (ι := ι) c := by sorry

end QuantumSDP18.MeasureBE
