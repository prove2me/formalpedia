-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_lemma3_8
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.lemma3_8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:06:35.35063+00:00
-- url     : https://prove2.me/theorems/ddd5e4b4-9784-403e-9088-62c1892e08f3
-- title:
--   Prediction when the nonzero transfer-matrix locations are known
-- statement:
--   Here $n\ge0$ is the number of qubits, $d=2^n$, states are positive semidefinite matrices of trace one, and $\mathcal N$ is a complex-linear CPTP map. The basis $Q=(Q_i)_{i=1}^{d^2}$ is a complete Hermitian Hilbert–Schmidt orthonormal basis. Write $R^Q_{ij}=\operatorname{tr}(Q_i\mathcal N(Q_j))$, $a_i=\operatorname{tr}(Q_i\rho)$ and $b_i=\operatorname{tr}(Q_iO)$. The norm $\|\cdot\|_2$ is the Hilbert–Schmidt norm, and $q=\max_i\|Q_i\|_\infty$ uses the spectral norm.
--
--   Let $\rho$ be any state and $O=O^\dagger$. A supplied finite support set $S$ has $|S|\le s$ and contains every nonzero entry of $R^Q$. Suppose the supplied estimates satisfy $|\widehat R_{ij}-R^Q_{ij}|\le\varepsilon$ on $S$, where $\varepsilon>0$. Then
--
--   $$\left|\sum_{(i,j)\in S}b_i\widehat R_{ij}a_j-\operatorname{tr}(O\mathcal N(\rho))\right|\le\varepsilon s\|O\|_2q.$$
--
--   This result requires knowledge that the omitted entries vanish; a numerical sparsity bound alone does not supply that knowledge.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 19, Lemma 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.19, Lemma 3.8. S is supplied and known to contain every nonzero
entry; off-support estimates are never used by the computed estimator. -/
theorem lemma3_8 {n : ℕ} (Q : HermitianBasis n) (N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F})
    (rho O : (Matrix (Qubits n) (Qubits n) ℂ)) (hrho : IsDensityMatrix rho) (hO : O.IsHermitian)
    (s : ℕ) (S : Finset (Fin (4 ^ n) × Fin (4 ^ n))) (hcard : S.card ≤ s)
    (hsupport : ∀ i j, (i,j) ∉ S → tm Q N i j = 0)
    (eps : ℝ) (heps : 0 < eps)
    (r : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℝ)
    (haccuracy : ∀ i j, (i,j) ∈ S → |r i j - tm Q N i j| ≤ eps) :
    |predictOn Q S r rho O - (O * N.val rho).trace.re| ≤
      eps * s * frobNorm O * basisNorm Q := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
