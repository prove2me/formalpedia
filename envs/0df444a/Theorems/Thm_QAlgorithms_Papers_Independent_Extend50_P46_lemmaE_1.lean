-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_lemmaE_1
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.lemmaE_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:16:16.450198+00:00
-- url     : https://prove2.me/theorems/699d3092-9a88-4d62-8a93-34b62e9b2f3f
-- title:
--   A memory-assisted Choi-copy lower bound for PTM learning
-- statement:
--   There are universal constants $c>0$ and $0<\varepsilon_0\le1/6$ such that, for every $n\ge1$ and $0<\varepsilon\le\varepsilon_0$, every joint-POVM algorithm on $T$ independent normalized Choi copies that estimates all PTM entries simultaneously within $\varepsilon$ with probability at least $2/3$ for every $n$-qubit CPTP channel satisfies
--
--   $$T\ge c\frac{n}{\varepsilon^2}.$$
--
--   The algorithm may retain and jointly measure all copies. Constants precede the dimension and the algorithm, and success is required separately on every channel. This establishes the optimal linear dependence on $n$ for memory-assisted Choi learning.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 60, Lemma E.1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.60-61, Lemma E.1. This lower bound applies to arbitrary joint
measurements with quantum memory, not just memoryless measurements. The entropy
argument at nonzero decoding error uses Fano's inequality; the asymptotic claim is unchanged. -/
theorem lemmaE_1 :
    ∃ c eps0 : ℝ, 0 < c ∧ 0 < eps0 ∧ eps0 ≤ 1/6 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
      ∀ P : ChoiLearner n (Matrix (ErrorMitigation.PauliIndex n) (ErrorMitigation.PauliIndex n) ℝ),
        (∀ N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F},

          (2 : ℝ)/3 ≤ choiReportEventProbability P N {r | tableGood r (ptm N) eps}) →
        c * n / eps^2 ≤ (P.copies : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
