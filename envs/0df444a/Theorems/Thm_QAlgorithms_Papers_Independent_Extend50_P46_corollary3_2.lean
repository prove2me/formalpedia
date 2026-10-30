-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_corollary3_2
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.corollary3_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:06:02.707636+00:00
-- url     : https://prove2.me/theorems/5e443ac2-b259-4df6-9344-05e0b7df0e5d
-- title:
--   Prediction for sparse states and observables
-- statement:
--   Here $n\ge0$ is the number of qubits, $d=2^n$, states are positive semidefinite matrices of trace one, and $\mathcal N$ is a complex-linear CPTP map. The basis $Q=(Q_i)_{i=1}^{d^2}$ is a complete Hermitian Hilbert–Schmidt orthonormal basis. Write $R^Q_{ij}=\operatorname{tr}(Q_i\mathcal N(Q_j))$, $a_i=\operatorname{tr}(Q_i\rho)$ and $b_i=\operatorname{tr}(Q_iO)$. The norm $\|\cdot\|_2$ is the Hilbert–Schmidt norm, and $q=\max_i\|Q_i\|_\infty$ uses the spectral norm.
--
--   Let $\rho$ be a state and $O=O^\dagger$ with at most $s_\rho$ and $s_O$ nonzero $Q$ coefficients, respectively. For $\varepsilon>0$, suppose $\widehat R$ estimates every entry of $R^Q$ within $\varepsilon$. Then
--
--   $$\left|\sum_{i,j}b_i\widehat R_{ij}a_j-\operatorname{tr}(O\mathcal N(\rho))\right|\le\varepsilon s_\rho\sqrt{s_O}\,\|O\|_2q.$$
--
--   This gives the sparsity dependence used in the learning results. A zero observable has the exact zero estimator.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 16, Corollary 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.16-17, Corollary 3.2. The factor is s_rho times sqrt(s_O),
and ||O||_2 is the Hilbert-Schmidt norm. -/
theorem corollary3_2 {n : ℕ} (Q : HermitianBasis n) (N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F})
    (rho O : (Matrix (Qubits n) (Qubits n) ℂ)) (hrho : IsDensityMatrix rho) (hO : O.IsHermitian)
    (srho sO : ℕ) (hrhoSparse : supportCount (coeff Q rho) ≤ srho)
    (hOSparse : supportCount (coeff Q O) ≤ sO)
    (eps : ℝ) (heps : 0 < eps)
    (r : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℝ)
    (haccuracy : tableGood r (tm Q N) eps) :
    |predict Q r rho O - (O * N.val rho).trace.re| ≤
      eps * srho * Real.sqrt sO * frobNorm O * basisNorm Q := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
