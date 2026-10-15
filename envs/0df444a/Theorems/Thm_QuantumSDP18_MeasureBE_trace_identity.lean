-- Prove2me | Theorems.Thm_QuantumSDP18_MeasureBE_trace_identity
-- name    : QuantumSDP18.MeasureBE.trace_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:32.544874+00:00
-- url     : https://prove2.me/theorems/d0bf389a-675b-4efd-a925-4fb19d879797
-- title:
--   §4.1, p. 25 — ρ ⊗ |0⟩⟨0|^{⊗a} = (I ⊗ |0⟩^{⊗a})ρ(I ⊗ ⟨0|^{⊗a}), so the acceptance probability is Tr(Kρ)
-- statement:
--   Let $\rho$ be any operator on the system register, attach $a$ ancilla qubits, and let $U$ be any operator on system and ancillas. Then attaching the ancillas in $|0\rangle$ is conjugation by the isometry $I\otimes|0\rangle^{\otimes a}$,
--
--   $$
--   \rho\otimes|0\rangle\langle 0|^{\otimes a} = (I\otimes|0\rangle^{\otimes a})\,\rho\,(I\otimes\langle 0|^{\otimes a}),
--   $$
--
--   and consequently the acceptance probability of the procedure equals the trace of $\rho$ against the block $K$:
--
--   $$
--   \operatorname{Tr}\Big((I\otimes|0\rangle\langle 0|)\,U\big(\rho\otimes|0\rangle\langle 0|^{\otimes a}\big)U^\dagger\Big)
--   = \operatorname{Tr}\Big(\big(I\otimes\langle 0|^{\otimes a}\big)U^\dagger(I\otimes|0\rangle\langle 0|)U\big(I\otimes|0\rangle^{\otimes a}\big)\rho\Big).
--   $$
--
--   This rewrites the bias condition (14) as a condition on the single operator $K - M$.
--
--   **Formalization Note** No hypothesis on $\rho$ or $U$ is needed; both identities hold for arbitrary matrices.
-- source:
--   van Apeldoorn and Gilyén, Improvements in quantum SDP-solving with applications, arXiv:1804.05058v1, p. 25, §4.1, 'Observe that …' and the display that follows

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_MeasureBE_Setting

namespace QuantumSDP18.MeasureBE

/-- §4.1, p. 25: `ρ ⊗ |0⟩⟨0|^{⊗a} = (I ⊗ |0⟩^{⊗a}) ρ (I ⊗ ⟨0|^{⊗a})`, and thus
`Tr((I ⊗ |0⟩⟨0|) U (ρ ⊗ |0⟩⟨0|^{⊗a}) U†) = Tr((I ⊗ ⟨0|^{⊗a}) U† (I ⊗ |0⟩⟨0|) U (I ⊗ |0⟩^{⊗a}) ρ)`. -/
theorem trace_identity {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℕ)
    (U : Matrix (ι × Anc c) (ι × Anc c) ℂ) (ρ : Matrix ι ι ℂ) :
    embedZero c ρ = ketZero (ι := ι) c * ρ * (ketZero (ι := ι) c).conjTranspose ∧
      accProb c U ρ = (blockK c U * ρ).trace := by sorry

end QuantumSDP18.MeasureBE
