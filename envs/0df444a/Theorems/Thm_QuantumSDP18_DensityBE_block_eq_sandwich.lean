-- Prove2me | Theorems.Thm_QuantumSDP18_DensityBE_block_eq_sandwich
-- name    : QuantumSDP18.DensityBE.block_eq_sandwich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:40.367935+00:00
-- url     : https://prove2.me/theorems/2e249f72-ae78-4dc4-bb25-fcaaeacf3b4f
-- title:
--   Proof of Lemma 12, display line 1 — the zero ancilla block of V
-- statement:
--   Let φ=G|0⟩ be the column of a matrix G at the all-zero input. The block of V obtained by fixing both the extra qubit and G's entire register to zero equals the SWAP sandwich formed with φ:
--
--   $$
--   (I\otimes\langle0|\langle\varphi|)S(I\otimes|0\rangle|\varphi\rangle).
--   $$
--
--   This identifies the block to be evaluated in the remaining steps of the proof. It is an algebraic identity for every complex matrix G; unitarity is used separately.
--
--   **Formalization Note** The system is the first factor of V, while the referenced block-encoding predicate expects the ancilla first. This theorem writes entries of the system-first block directly. The ancilla is the extra qubit followed by G's w+1+c qubits.
-- source:
--   van Apeldoorn and Gilyén, Improvements in quantum SDP-solving with applications, arXiv:1804.05058v1, p. 16, proof of Lemma 12, display line 1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_DensityBE_Setting

namespace QuantumSDP18.DensityBE

theorem block_eq_sandwich {w c : ℕ} (G : Matrix (Reg w c) (Reg w c) ℂ) :
    (Matrix.of fun i j : QAlgorithms.Qubits w =>
      V G ((i, false), zeroReg w c) ((j, false), zeroReg w c)) =
    sandwich (purifVec G) := by sorry

end QuantumSDP18.DensityBE
