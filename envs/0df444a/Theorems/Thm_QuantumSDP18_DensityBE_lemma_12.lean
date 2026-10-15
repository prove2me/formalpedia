-- Prove2me | Theorems.Thm_QuantumSDP18_DensityBE_lemma_12
-- name    : QuantumSDP18.DensityBE.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:36.057502+00:00
-- url     : https://prove2.me/theorems/43c554cd-ffc3-4b64-9bce-f96854f58c19
-- title:
--   Lemma 12 — exact block-encoding of a subnormalized density operator (proof’s corrected ancilla count)
-- statement:
--   Let G be a unitary on w+a qubits, where a=c+1 includes a one-qubit flag, and suppose G|0⟩ is a purification of the subnormalized w-qubit density operator ϱ. Form V by preparing this state with G, swapping the initial w-qubit system and extra qubit with the system-and-flag part of the prepared register, then applying G†. The resulting unitary is an exact block-encoding of ϱ:
--
--   $$
--   \left\|\varrho-(I\otimes\langle0|^{\otimes(w+a+1)})V(I\otimes|0\rangle^{\otimes(w+a+1)})\right\|=0.
--   $$
--
--   This converts purified access to a subnormalized density operator into the operator input model used by the paper.
--
--   **Formalization Note** The published block-encoding predicate is used after reindexing V to put the ancillas first; it includes V's unitarity. The ancilla type has 1+w+a qubits. The paper prints w+a in Lemma 12, while its proof takes a 1+w+a-qubit zero block of a (2w+a+1)-qubit V. The statement uses the proof's count. The purification and subnormalization hypotheses are both explicit as in the page, although purification implies subnormalization and G's unitarity implies its vector has norm one. The construction contains one G and one G†; gate count is outside this matrix statement.
-- source:
--   van Apeldoorn and Gilyén, Improvements in quantum SDP-solving with applications, arXiv:1804.05058v1, p. 15, Lemma 12; p. 16, proof and first display

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_DensityBE_Setting

namespace QuantumSDP18.DensityBE

theorem lemma_12 {w c : ℕ} (G : Matrix (Reg w c) (Reg w c) ℂ)
    (ϱ : Matrix (QAlgorithms.Qubits w) (QAlgorithms.Qubits w) ℂ)
    (hG : G ∈ Matrix.unitaryGroup (Reg w c) ℂ)
    (hϱ : IsSubnormDensity ϱ)
    (hpur : IsPurification (purifVec G) ϱ) :
    QAlgorithms.IsBlockEncoding (ancZero w c)
      (Matrix.reindex (blockEquiv w c) (blockEquiv w c) (V G)) 1 0 ϱ := by sorry

end QuantumSDP18.DensityBE
