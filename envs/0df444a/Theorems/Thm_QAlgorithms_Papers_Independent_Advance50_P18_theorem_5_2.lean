-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_theorem_5_2
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.theorem_5_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:48:36.493828+00:00
-- url     : https://prove2.me/theorems/e1a473ae-fe38-4c9d-8b40-80ab2c7104c0
-- title:
--   Theorem 5.2: quantum-to-classical private-channel reduction
-- statement:
--   Suppose a private quantum channel encrypts every unit $n$-qubit vector using $N$ keys with law $p_i$, a fixed mixed $a$-qubit ancilla $\rho_a$, and full-output density $\rho_0$ on $n+a$ qubits. There exists a new family of fixed unitaries $U_i'$ on $2n+a$ qubits, using exactly the same key labels, law, and ancilla, such that every $2n$-bit computational-basis message $|x\rangle$ satisfies
--
--   $$\sum_{i=1}^N p_iU_i'(|x\rangle\langle x|\otimes\rho_a)(U_i')^\dagger=(I_{2^n}/2^n)\otimes\rho_0.$$
--
--   The new unitaries give exact keyed recovery. The first $2n$ message qubits are represented as two $n$-qubit registers; the displayed output is reassociated onto those same registers and the unchanged ancilla. This reduction preserves the entire probability law, rather than only its entropy.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 6, Theorem 5.2: quantum-to-classical private-channel reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF pp.6–7, Theorem 5.2: a PQC for n qubits yields one for 2n classical bits,
with exactly the same key law and mixed ancilla. The full output is I/2^n tensor rho0.
The proof's C_(2^(2n)) at p.6 for off-diagonal inputs is a dimensional typo for C_(2^n);
the p.7 y,z sums range over every index. Neither typo changes the theorem stated here. -/
theorem theorem_5_2 (n a N : ℕ)
    (E : KeyedUnitaryEnsemble (Fin N) (Qubits n × Qubits a))
    (anc : (Matrix (Qubits a) (Qubits a) ℂ)) (rho0 : (Matrix (Qubits n × Qubits a) (Qubits n × Qubits a) ℂ))
    (h : PQC (allPure (Qubits n)) E anc rho0) :
    ∃ Eprime : KeyedUnitaryEnsemble (Fin N) ((Qubits n × Qubits n) × Qubits a),
      Eprime.p = E.p ∧
      PQC (classicalSource (Qubits n × Qubits n)) Eprime anc (reductionOutput rho0) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
