-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_optimal_private_quantum_channel
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.optimal_private_quantum_channel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:44:30.739809+00:00
-- url     : https://prove2.me/theorems/00c2dd4b-b54b-495d-abc8-3382ed96f765
-- title:
--   Abstract and §7: optimal private quantum one-time pad
-- statement:
--   For every nonnegative integer $n$, the quantum one-time pad encrypts every $n$-qubit state using a shared classical key of entropy exactly $2n$ bits. Its encoder is chosen independently of the message: select $x\in\{0,1,2,3\}^n$ uniformly and conjugate by $\bar\sigma_x=\sigma_{x_1}\otimes\cdots\otimes\sigma_{x_n}$. There is no ancilla, and for every density matrix $\rho$,
--
--   $$\sum_x 2^{-2n}\bar\sigma_x\rho\bar\sigma_x^\dagger=I_{2^n}/2^n,\qquad H(p)=2n.$$
--
--   Conversely, let a private quantum channel for all unit $n$-qubit vectors use $N$ keys with probabilities $p_i$, input-independent full-space unitaries, an arbitrary fixed mixed $a$-qubit ancilla, and any fixed full-output density. Then
--
--   $$H(p)\ge 2n,\qquad N\ge 2^{2n}.$$
--
--   Here $H(p)=-\sum_i p_i\log_2 p_i$, with $0\log_2 0=0$. The ancilla is independent of both input and key and is included in the transmitted system. Unitary inversion gives exact recovery. This combines the paper’s achieving scheme and its unrestricted lower bound.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 1, Abstract and §7: optimal private quantum one-time pad

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- Abstract (PDF p.1), §7 (p.9), Theorem 4.1 (p.5) and Corollary 5.4 (p.8):
full tensor-Pauli encryption attains 2n bits without ancilla, including mixed inputs;
every exact PQC, with any finite mixed ancilla, requires at least 2n bits. -/
theorem optimal_private_quantum_channel (n : ℕ) :
    (∃ E : KeyedUnitaryEnsemble (Fin n → Fin 4) (Qubits n), E = fullPauli n ∧
      BarePQC (allPure (Qubits n)) E (sourceMixedIdentity (Qubits n)) ∧
      keyEntropy E.p = 2 * (n : ℝ) ∧
      ∀ rho : (Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho →
        encrypt E rho = sourceMixedIdentity (Qubits n)) ∧
    (∀ (a N : ℕ) (E : KeyedUnitaryEnsemble (Fin N) (Qubits n × Qubits a))
      (anc : (Matrix (Qubits a) (Qubits a) ℂ)) (rho0 : (Matrix (Qubits n × Qubits a) (Qubits n × Qubits a) ℂ)),
      PQC (allPure (Qubits n)) E anc rho0 →
      2 * (n : ℝ) ≤ keyEntropy E.p ∧ 2 ^ (2 * n) ≤ N) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
