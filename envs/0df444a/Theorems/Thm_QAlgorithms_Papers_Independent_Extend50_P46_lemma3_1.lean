-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_lemma3_1
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.lemma3_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:05:27.488854+00:00
-- url     : https://prove2.me/theorems/a024b5c6-e8a9-4c76-907b-ce500291aec7
-- title:
--   Prediction from entrywise transfer-matrix estimates
-- statement:
--   Here $n\ge0$ is the number of qubits, $d=2^n$, states are positive semidefinite matrices of trace one, and $\mathcal N$ is a complex-linear CPTP map. The basis $Q=(Q_i)_{i=1}^{d^2}$ is a complete Hermitian Hilbert–Schmidt orthonormal basis. Write $R^Q_{ij}=\operatorname{tr}(Q_i\mathcal N(Q_j))$, $a_i=\operatorname{tr}(Q_i\rho)$ and $b_i=\operatorname{tr}(Q_iO)$. The norm $\|\cdot\|_2$ is the Hilbert–Schmidt norm, and $q=\max_i\|Q_i\|_\infty$ uses the spectral norm.
--
--   Let $\rho$ be a state and $O=O^\dagger$. Suppose $B_\rho=\sum_i|a_i|>0$, $B_O=\sum_i|b_i|>0$, and a supplied table $\widehat R$ satisfies $|\widehat R_{ij}-R^Q_{ij}|\le\varepsilon$ for every matching index pair, with $\varepsilon>0$. The estimator computed from that table satisfies
--
--   $$\widehat\mu=\sum_{i,j}b_i\widehat R_{ij}a_j,\qquad |\widehat\mu-\operatorname{tr}(O\mathcal N(\rho))|\le\varepsilon B_\rho B_O.$$
--
--   This converts coordinate errors to prediction errors without using the true expectation in the estimator.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 15, Lemma 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.15, Lemma 3.1. The matching-index error assumption corrects the
index slip after Eq.(3.4); Eqs.(3.3),(3.5) fix the intended estimator. -/
theorem lemma3_1 {n : ℕ} (Q : HermitianBasis n) (N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F})
    (rho O : (Matrix (Qubits n) (Qubits n) ℂ)) (hrho : IsDensityMatrix rho) (hO : O.IsHermitian)
    (eps Brho BO : ℝ) (heps : 0 < eps) (hBrho : 0 < Brho) (hBO : 0 < BO)
    (hrhoNorm : ∑ i, |coeff Q rho i| = Brho)
    (hONorm : ∑ i, |coeff Q O i| = BO)
    (r : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℝ)
    (haccuracy : tableGood r (tm Q N) eps) :
    |predict Q r rho O - (O * N.val rho).trace.re| ≤ eps * Brho * BO := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
