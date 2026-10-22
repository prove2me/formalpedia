-- Prove2me | Theorems.Thm_QuantumSDP18_DensityBE_V_mem_unitaryGroup
-- name    : QuantumSDP18.DensityBE.V_mem_unitaryGroup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:24.347733+00:00
-- url     : https://prove2.me/theorems/c08f1669-e33b-4f7e-aad0-87b439ea480d
-- title:
--   Proof of Lemma 12 — the constructed V is unitary
-- statement:
--   Let G be a unitary on the w-qubit system, one flag qubit, and c junk qubits. Let S exchange the initial system-and-extra-qubit register with the system-and-flag part of G's register, leaving the junk fixed. Set
--
--   $$
--   V=(I\otimes G^{\dagger})S(I\otimes G).
--   $$
--
--   Then V is unitary on the combined register. This supplies the unitary part of the block-encoding constructed in Lemma 12.
--
--   **Formalization Note** The combined register has 2w+c+2=2w+a+1 qubits with a=c+1. Its order is (system, extra qubit, G's system, flag, junk). The paper prints an identity factor on a qubits beside the swap; the factor left fixed here has c=a−1 qubits, as required by the stated total size.
-- source:
--   van Apeldoorn and Gilyén, Improvements in quantum SDP-solving with applications, arXiv:1804.05058v1, p. 16, proof of Lemma 12, sentence beginning “Consider”

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_DensityBE_Setting

namespace QuantumSDP18.DensityBE

theorem V_mem_unitaryGroup {w c : ℕ} (G : Matrix (Reg w c) (Reg w c) ℂ)
    (hG : G ∈ Matrix.unitaryGroup (Reg w c) ℂ) :
    V G ∈ Matrix.unitaryGroup (Big w c) ℂ := by sorry

end QuantumSDP18.DensityBE
