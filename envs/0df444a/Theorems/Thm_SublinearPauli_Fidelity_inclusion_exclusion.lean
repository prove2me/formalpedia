-- Prove2me | Theorems.Thm_SublinearPauli_Fidelity_inclusion_exclusion
-- name    : SublinearPauli.Fidelity.inclusion_exclusion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:41:50.877644+00:00
-- url     : https://prove2.me/theorems/ee86ea5e-0329-4dfd-ae17-37fa4818a688
-- title:
--   Observation 3 — inclusion–exclusion for compatible Pauli words
-- statement:
--   Let $Q,Q'$ be $N$-qubit Pauli words with $(Q,Q')\in\mathcal S$, i.e. at every qubit the letters agree or one of them is $I$. Then
--   $$w(Q)+w(Q')-w(Q\cup Q')=\sum_{i=1}^N\Bigl(\mathbf 1\{Q_i\ne I\}+\mathbf 1\{Q'_i\ne I\}-\mathbf 1\{Q_i\ne I\vee Q'_i\ne I\}\Bigr)=\sum_{i=1}^N\mathbf 1\{Q_i=Q'_i\ne I\}=w(Q\cap Q').$$
--
--   This identity converts the count $3^{N-w(Q)}\cdot 3^{N-w(Q')}/3^{N-w(Q\cup Q')}$ into $3^{N-w(Q\cap Q')}$ in the proof of Lemma 2.
--
--   **Formalization Note** The identity is stated in the integers, so the subtraction is not truncated; all three equalities of the chain are asserted.
--
--   Differences from the source:
--   - encoding: Pauli words in $\{X,Y,Z,I\}^{\otimes N}$ with qubits $1,\dots,N$ → functions from Fin N to the four letters, qubits $0,\dots,N-1$, and $\cap,\cup$ total functions agreeing with the paper on compatible pairs; reason: Lean convention, the same pairs and values on $\mathcal S$.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, p.10, Observation 3

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Pauli

open ClassicalShadow.Linear

namespace SublinearPauli.Fidelity

/-- **Observation 3** (Inclusion–exclusion with Pauli observables), p.10. For every compatible
pair `(Q, Q') ∈ 𝒮`,
`w(Q) + w(Q') − w(Q ∪ Q') = Σ_i (1{Q_i ≠ I} + 1{Q'_i ≠ I} − 1{Q_i ≠ I ∨ Q'_i ≠ I})
  = Σ_i 1{Q_i = Q'_i ≠ I} = w(Q ∩ Q')`, computed in `ℤ`. -/
theorem inclusion_exclusion {N : ℕ} (Q Q' : PauliString N) (h : Compatible Q Q') :
    ((weight Q : ℤ) + weight Q' - weight (union Q Q') =
      ∑ i, ((if Q i ≠ Letter.I then (1 : ℤ) else 0) + (if Q' i ≠ Letter.I then 1 else 0) -
        (if Q i ≠ Letter.I ∨ Q' i ≠ Letter.I then 1 else 0))) ∧
    (∑ i, ((if Q i ≠ Letter.I then (1 : ℤ) else 0) + (if Q' i ≠ Letter.I then 1 else 0) -
        (if Q i ≠ Letter.I ∨ Q' i ≠ Letter.I then 1 else 0)) =
      ∑ i, (if Q i = Q' i ∧ Q i ≠ Letter.I then (1 : ℤ) else 0)) ∧
    (∑ i, (if Q i = Q' i ∧ Q i ≠ Letter.I then (1 : ℤ) else 0) = weight (inter Q Q')) := by sorry

end SublinearPauli.Fidelity
