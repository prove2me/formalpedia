-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_remark3_10
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.remark3_10
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:18:12.457994+00:00
-- url     : https://prove2.me/theorems/d673cada-46a9-4b83-a03b-01089ca0dc85
-- title:
--   Sparse transfer matrices have low image rank and high Choi rank
-- statement:
--   Here $n\ge0$ is the number of qubits, $d=2^n$, states are positive semidefinite matrices of trace one, and $\mathcal N$ is a complex-linear CPTP map. The basis $Q=(Q_i)_{i=1}^{d^2}$ is a complete Hermitian Hilbert–Schmidt orthonormal basis. Write $R^Q_{ij}=\operatorname{tr}(Q_i\mathcal N(Q_j))$, $a_i=\operatorname{tr}(Q_i\rho)$ and $b_i=\operatorname{tr}(Q_iO)$. The norm $\|\cdot\|_2$ is the Hilbert–Schmidt norm, and $q=\max_i\|Q_i\|_\infty$ uses the spectral norm.
--
--   There is an absolute $c>0$ such that whenever the $Q$-TM has at most $s$ nonzero entries,
--
--   $$\dim_{\mathbb C}\operatorname{im}(\mathcal N)\le s,\qquad\operatorname{rank}J(\mathcal N)\ge\frac{c}{sq^4}.$$
--
--   For Pauli sparsity at most $s$, the same universal constant may be chosen so that
--
--   $$\operatorname{rank}J(\mathcal N)\ge c\frac{4^n}{s}.$$
--
--   The first rank is that of the superoperator as a linear map on matrices; the second is the matrix rank of its normalized Choi state, equivalently its Kraus rank. The general-basis form follows the product ONB in Eq.(B.2); its constant is existential because the remark supplies no sharp constant.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 20, Remark 3.10: low superoperator rank and high Choi rank

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.20-21, Remark 3.10: low superoperator rank and high Choi rank
are separate conclusions. The unprinted general-basis extension is expressed
with an existential uniform constant, not an invented printed sharp constant. -/
theorem remark3_10 :
    ∃ c : ℝ, 0 < c ∧
    (∀ {n : ℕ} (Q : HermitianBasis n) (N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F}) (s : ℕ),
      supportCount (fun ij : Fin (4 ^ n) × Fin (4 ^ n) => tm Q N ij.1 ij.2) ≤ s →
        Module.finrank ℂ (LinearMap.range N.val) ≤ s ∧
        c / ((s : ℝ) * basisNorm Q ^ 4) ≤ ((idTensorSuperop (R := Qubits n) N.val (pureDensity (maxEntangled n))).rank : ℝ)) ∧
    (∀ {n : ℕ} (N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F}) (s : ℕ),
      supportCount (fun ij : ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n => ptm N ij.1 ij.2) ≤ s →
        c * (4 : ℝ)^n / s ≤ ((idTensorSuperop (R := Qubits n) N.val (pureDensity (maxEntangled n))).rank : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
