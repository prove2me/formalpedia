-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_theorem4_1
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.theorem4_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:07:06.504694+00:00
-- url     : https://prove2.me/theorems/72e3e919-d7af-43fd-8c06-9ef6eb6f8d11
-- title:
--   Learning all Pauli transfer-matrix entries with quantum memory
-- statement:
--   The unknown channel is an arbitrary complex-linear CPTP map on $n$ qubits. Choi access supplies independent copies of the normalized reference-first state $J(\mathcal N)=(\mathrm{id}\otimes\mathcal N)(|\Omega\rangle\langle\Omega|)$. The algorithm is a joint POVM on exactly its stated number of copies, chosen before the channel. Accuracy means simultaneous absolute error under its actual Born law. All constants, and all exponents hidden in $\widetilde O$, are uniform before the channel, dimension, basis and accuracy parameters. Assume $\varepsilon>0$ and $0<\delta<1$.
--
--   Write $P_A$ for the Pauli string with label $A\in\{I,X,Y,Z\}^n$, and $R^P_{AB}=2^{-n}\operatorname{tr}(P_A\mathcal N(P_B))$. There is a learner, independent of the unknown channel, using
--
--   $$m=O\!\left(\frac{n+\log(1/\delta)}{\varepsilon^4}\right)$$
--
--   copies and returning estimates with $|\widehat R_{AB}-R^P_{AB}|\le\varepsilon$ for all $A,B$ simultaneously with probability at least $1-\delta$. This is a sample bound; printing the full table has no claimed efficient time bound.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 21, Theorem 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.21, Theorem 4.1: an unknown-channel-independent joint measurement.
There is no time bound for printing the entire table. -/
theorem theorem4_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ eps delta : ℝ,
      0 < eps → 0 < delta → delta < 1 →
      ∃ P : ChoiLearner n (Matrix (ErrorMitigation.PauliIndex n) (ErrorMitigation.PauliIndex n) ℝ),
        (P.copies : ℝ) ≤ C * (n + Real.log delta⁻¹) / eps^4 ∧
        ∀ N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F},

          1 - delta ≤ choiReportEventProbability P N {r | tableGood r (ptm N) eps} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
