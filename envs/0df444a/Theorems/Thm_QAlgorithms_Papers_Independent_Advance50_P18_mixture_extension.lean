-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_mixture_extension
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.mixture_extension
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:45:14.770433+00:00
-- url     : https://prove2.me/theorems/e74eb7f0-3115-40c4-aa85-9002695d5f4f
-- title:
--   §3, unnumbered: security extends to mixtures of source states
-- statement:
--   Let $S$ be a set of unit $n$-qubit vectors, and let a private quantum channel use a finite key law $p_i$, fixed full-space unitaries $U_i$, a fixed mixed ancilla $\rho_a$, and fixed full output $\rho_0$. Let $\rho$ be any finite mixture of source states: $\rho=\sum_j q_j|\psi_j\rangle\langle\psi_j|$, where $\psi_j\in S$, $q_j\ge0$, and $\sum_jq_j=1$. Then the same channel satisfies
--
--   $$\sum_i p_iU_i(\rho\otimes\rho_a)U_i^\dagger=\rho_0.$$
--
--   For every key $i$, conjugating its encoded state by $U_i^\dagger$ recovers $\rho\otimes\rho_a$ exactly. Thus the same key distribution and ancilla securely convey every mixture of $S$-states. This conclusion does not enlarge a restricted source to all density matrices.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 4, §3, unnumbered: security extends to mixtures of source states

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.4, §3: the same scheme and fixed output work on all finite mixtures of S-states;
conjugation by the inverse keyed unitary recovers the message and its original ancilla. -/
theorem mixture_extension (n a N : ℕ) (S : Set ((EuclideanSpace ℂ (Qubits n))))
    (E : KeyedUnitaryEnsemble (Fin N) (Qubits n × Qubits a))
    (anc : (Matrix (Qubits a) (Qubits a) ℂ)) (rho0 : (Matrix (Qubits n × Qubits a) (Qubits n × Qubits a) ℂ))
    (h : PQC S E anc rho0) (rho : (Matrix (Qubits n) (Qubits n) ℂ)) (hmix : IsSourceMixture S rho) :
    encrypt E (Matrix.kronecker rho anc) = rho0 ∧
    ∀ i : Fin N, (E.U i).conjTranspose *
      (E.U i * Matrix.kronecker rho anc * (E.U i).conjTranspose) * E.U i =
        Matrix.kronecker rho anc := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
