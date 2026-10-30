-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_appendixE_sparse_extension
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.appendixE_sparse_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:17:03.006665+00:00
-- url     : https://prove2.me/theorems/e4cebecf-e1a4-4e5a-862d-31bc9c6c198a
-- title:
--   Memory-assisted lower bounds for sparse unital channels and sparse prediction
-- statement:
--   There are universal $c>0$ and $0<\varepsilon_0\le1/6$ such that the following two lower bounds hold for every $n\ge1$ and $0<\varepsilon\le\varepsilon_0$. The unknown CPTP channel is promised unital with at most two nonzero PTM entries; the promise is uniform and its support is unknown.
--
--   1. Every joint-POVM Choi learner that estimates every PTM entry within $\varepsilon$, simultaneously with probability at least $2/3$ on every promised channel, uses $T\ge cn/\varepsilon^2$ copies.
--   2. The same bound holds for any classical-report joint-POVM learner and decoder that, with simultaneous success probability at least $2/3$ on every promised channel, predicts $\operatorname{tr}(O\mathcal N(\rho))$ within $\varepsilon$ for all states with Pauli sparsity at most two and Hermitian observables with Pauli sparsity at most one and $\|O\|_2\le\sqrt{2^n}$.
--
--   Thus both tasks satisfy
--
--   $$T=\Omega(n/\varepsilon^2)$$
--
--   even with quantum memory. There is no entanglement-breaking hypothesis in this statement.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 61, Appendix E, unnumbered sparse-channel and sparse-prediction lower bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.61, final paragraph: both memory-assisted lower bounds under the
unital constant-sparse promise. The D.4 ensemble has 2(4^n-1)^2 signed elements,
correcting the count printed in this paragraph. No entanglement-breaking promise is added. -/
theorem appendixE_sparse_extension :
    ∃ c eps0 : ℝ, 0 < c ∧ 0 < eps0 ∧ eps0 ≤ 1/6 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
      (∀ P : ChoiLearner n (Matrix (ErrorMitigation.PauliIndex n) (ErrorMitigation.PauliIndex n) ℝ),
        (∀ N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F}, N.val 1 = 1 →
          supportCount (fun ij : ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n => ptm N ij.1 ij.2) ≤ 2 →

          (2 : ℝ)/3 ≤ choiReportEventProbability P N {r | tableGood r (ptm N) eps}) →
        c * n / eps^2 ≤ (P.copies : ℝ)) ∧
      (∀ (Out : Type) (P : ChoiLearner n Out)
        (decode : Out → (Matrix (Qubits n) (Qubits n) ℂ) → (Matrix (Qubits n) (Qubits n) ℂ) → ℝ),
        (∀ N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F}, N.val 1 = 1 →
          supportCount (fun ij : ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n => ptm N ij.1 ij.2) ≤ 2 →
          let E := {r | ∀ rho O : (Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho → O.IsHermitian →
            supportCount (ErrorMitigation.pauliStateVector rho) ≤ 2 →
            supportCount (ErrorMitigation.pauliObservableRow O) ≤ 1 →
            frobNorm O ≤ Real.sqrt ((2 : ℝ)^n) →
            |decode r rho O - (O * N.val rho).trace.re| ≤ eps}
          (2 : ℝ)/3 ≤ choiReportEventProbability P N E) →
        c * n / eps^2 ≤ (P.copies : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
