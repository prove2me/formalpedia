-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_collectivePauli_delta
-- name    : QAlgorithms.Papers.Independent.Support50.P30.collectivePauli_delta
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:21:56.101063+00:00
-- url     : https://prove2.me/theorems/9d7c2bc1-f184-4d9e-990c-cb45c8c8b697
-- title:
--   Theorem 2 (Exact Delta values for collective Pauli operators)
-- statement:
--   Fix an orthonormal Schur decomposition on $n$ qubits, a sector $\lambda=(n-m,m)$ of dimension $d_\lambda=n-2m+1$, and one Pauli matrix $\chi\in\{X,Y,Z\}$. Compress the following unnormalized permutation-equivariant operators to their common $\lambda$ block. With $\Delta(B)=\operatorname{Tr}(B^2)-\operatorname{Tr}(B)^2/d_\lambda$,
--
--   $$\Delta\!\left(\left[\sum_j\chi_j\right]_\lambda\right)=2\binom{d_\lambda+1}{3},\quad
--   \Delta\!\left(\left[\sum_{k<j}\chi_j\chi_k\right]_\lambda\right)=\frac83\binom{d_\lambda+2}{5},\quad
--   \Delta\!\left(\left[\prod_j\chi_j\right]_\lambda\right)=\frac{d_\lambda^2-1+(n\bmod2)}{d_\lambda}.$$
--
--   These exact values apply before the normalization factors in Eqs. (9) and (10). In particular the one-dimensional sectors have zero statistic, as do the two-dimensional sectors for the pair sum.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 6, Theorem 2 (Exact Delta values for collective Pauli operators)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

/-- PDF pp.6,27-28, Theorem 2: unnormalized sums/products. The intermediate
trace typos on p.28 do not enter these final Delta identities. -/
theorem collectivePauli_delta {n : ℕ} (S : SchurFrame n) (m : Sector n)
    (chi : Matrix Bool Bool ℂ) (hchi : chi ∈ ({pauliX, pauliY, pauliZ} : Set _)) :
    centeredDelta (commonBlock S m (collective n chi 1)) =
        2 * (((blockDim n m + 1).choose 3 : ℕ) : ℝ) ∧
    centeredDelta (commonBlock S m (collective n chi 2)) =
        (8 / 3 : ℝ) * (((blockDim n m + 2).choose 5 : ℕ) : ℝ) ∧
    centeredDelta (commonBlock S m (collective n chi n)) =
        ((blockDim n m : ℝ) ^ 2 - 1 + ((n % 2 : ℕ) : ℝ)) / (blockDim n m : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
