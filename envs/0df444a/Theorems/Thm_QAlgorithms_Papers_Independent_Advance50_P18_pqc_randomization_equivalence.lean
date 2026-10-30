-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_pqc_randomization_equivalence
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.pqc_randomization_equivalence
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:51:57.984997+00:00
-- url     : https://prove2.me/theorems/0cbcf94a-1077-4370-9f3b-1e8911a2f882
-- title:
--   §6, unnumbered: PQCs and source randomization are the same model
-- statement:
--   Fix a source $S$ of unit $n$-qubit vectors, a finite classical key law $p_i$, full-space keyed unitaries $U_i$, a fixed mixed ancilla $\rho_a$, and a fixed full-output density $\rho_0$. These data form a private quantum channel if and only if applying the selected unitary and forgetting only its classical label randomizes the source to $\rho_0$. Both conditions mean exactly
--
--   $$\sum_i p_iU_i(|\psi\rangle\langle\psi|\otimes\rho_a)U_i^\dagger=\rho_0\quad(\psi\in S).$$
--
--   All density and normalization requirements are included in each predicate. The ancillary environment remains in the output. The entropy cost is the Shannon entropy of the same law $p_i$. This identifies the two models without introducing a free discarded environment.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 8, §6, unnumbered: PQCs and source randomization are the same model

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.8, §6: PQC and randomization are the same exact full-output condition,
with the same source, law, unitaries, mixed ancilla and fixed output. -/
theorem pqc_randomization_equivalence (n a N : ℕ) (S : Set ((EuclideanSpace ℂ (Qubits n))))
    (E : KeyedUnitaryEnsemble (Fin N) (Qubits n × Qubits a))
    (anc : (Matrix (Qubits a) (Qubits a) ℂ)) (rho0 : (Matrix (Qubits n × Qubits a) (Qubits n × Qubits a) ℂ)) :
    PQC S E anc rho0 ↔ ExactSourceRandomization S E anc rho0 := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
