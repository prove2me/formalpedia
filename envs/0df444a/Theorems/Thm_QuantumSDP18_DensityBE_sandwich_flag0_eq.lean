-- Prove2me | Theorems.Thm_QuantumSDP18_DensityBE_sandwich_flag0_eq
-- name    : QuantumSDP18.DensityBE.sandwich_flag0_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:23.66155+00:00
-- url     : https://prove2.me/theorems/ee333878-4395-4e8d-a426-307ceaff3b89
-- title:
--   Proof of Lemma 12, display lines 3–7 — the SWAP sandwich equals ϱ
-- statement:
--   Let φ purify a subnormalized w-qubit density operator ϱ: the flag-zero block of the partial trace of |φ⟩⟨φ| over the junk register is ϱ. If φ₀ is φ with its flag-one amplitudes set to zero, then the SWAP sandwich of φ₀ is exactly ϱ:
--
--   $$
--   (I\otimes\langle0|\langle\varphi_0|)S(I\otimes|0\rangle|\varphi_0\rangle)=\varrho.
--   $$
--
--   This is the final matrix identity needed for the zero-error block-encoding.
--
--   **Formalization Note** The paper evaluates this expression through a Schmidt decomposition. The statement uses the purification condition directly and therefore requires no decomposition data. The matrix entries are Σₜ φ(i,0,t) overline{φ(j,0,t)}; the conjugation order is essential for complex operators.
-- source:
--   van Apeldoorn and Gilyén, Improvements in quantum SDP-solving with applications, arXiv:1804.05058v1, p. 16, proof of Lemma 12, display lines 3–7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_DensityBE_Setting

namespace QuantumSDP18.DensityBE

theorem sandwich_flag0_eq {w c : ℕ} (φ : Reg w c → ℂ)
    (ϱ : Matrix (QAlgorithms.Qubits w) (QAlgorithms.Qubits w) ℂ)
    (hpur : IsPurification φ ϱ) :
    sandwich (flag0 φ) = ϱ := by sorry

end QuantumSDP18.DensityBE
