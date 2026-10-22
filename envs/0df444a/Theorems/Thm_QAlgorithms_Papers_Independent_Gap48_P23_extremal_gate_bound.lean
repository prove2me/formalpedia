-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_extremal_gate_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.extremal_gate_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:09:29.599473+00:00
-- url     : https://prove2.me/theorems/83af3a62-3fef-4079-8ac2-d8f1e1745924
-- title:
--   Lemma E.6.
-- statement:
--   For $\ell\ge1$, input covariance is with $T^\ell(U)$ and output covariance with $U$, for every $U\in U(2)$. The channel $\Phi_{\rm Tr}^\ell$ embeds through $V^\ell$ and keeps the first qubit; $\Phi_{\rm UNOT}^\ell$ measures the normalized coherent-state POVM and prepares the orthogonal state. Let $D_\ell$ be the explicit real dual Clebsch–Gordan matrix (C.49),(C.54). The unnormalized Choi order is output tensor input.
--
--   There are constants $C>0,N$ such that for every $\ell\ge\max\{1,N\}$ the two physical channels on binary encoded $(\ell+1)$-dimensional inputs have exact one-qubit/CNOT gate-list realizations with
--   $$\operatorname{size}(\Phi_{\rm Tr}^\ell),\operatorname{size}(\Phi_{\rm UNOT}^\ell)\le C\ell\log\ell.$$
--   The construction uses real controlled rotations and modular shifts, with identity padding on unused binary labels. Ancillas start in zero and the environment is discarded.
--
--   This characterizes the physical postprocessing maps used in the template algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 78, Lemma E.6.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.78-79, Lemma E.6: exact implementations on binary encoded input
registers. The supplied input embedding is zero on unused binary labels;
controlled rotations and modular shifts use the identity padding above. The
threshold excludes ell=1 where ell log ell=0. -/
theorem extremal_gate_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ ell ≥ N, 1 ≤ ell →
      ∃ A B : OneOutputCircuit (Nat.clog 2 (ell+1)),
        circuitOutput A (finiteRegisterEmbedding (ell+1)) = partialTraceChannel ell ∧
        circuitOutput B (finiteRegisterEmbedding (ell+1)) = universalNotChannel ell ∧
        (A.circuit.size : ℝ) ≤ C * ell * Real.log ell ∧
        (B.circuit.size : ℝ) ≤ C * ell * Real.log ell ∧
        (∀ z y : Qubits (1+Nat.clog 2 (ell+1)),
          (∀ a, controlledBinaryEmbedding ell z a = 0) →
          paddedRotation ell z y = (1 : Op (Qubits (1+Nat.clog 2 (ell+1)))) z y ∧
          paddedDecrement ell z y = (1 : Op (Qubits (1+Nat.clog 2 (ell+1)))) z y) ∧
        (∀ z y : Qubits (1+Nat.clog 2 ((ell+1)+1)),
          (∀ a, controlledBinaryEmbedding (ell+1) z a = 0) →
          paddedIncrement ell z y = (1 : Op (Qubits (1+Nat.clog 2 ((ell+1)+1)))) z y) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
