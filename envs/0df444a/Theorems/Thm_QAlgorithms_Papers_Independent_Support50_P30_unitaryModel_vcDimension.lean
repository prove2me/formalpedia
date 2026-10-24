-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_unitaryModel_vcDimension
-- name    : QAlgorithms.Papers.Independent.Support50.P30.unitaryModel_vcDimension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:29:52.173024+00:00
-- url     : https://prove2.me/theorems/ff842a32-9f7e-4dba-a1a3-1411df9f0faa
-- title:
--   Theorem 7 (VC dimension for the unitary Sn model)
-- statement:
--   Let $n\ge2$ and fix a layered generator schedule from Eq. (9), a Hermitian measurement $O$ from Eq. (10), and a real threshold $b$. The classifiers act on all $n$-qubit density matrices, including mixed states, by $h_\theta(\rho)=\mathbf1\{\operatorname{Tr}(U(\theta)\rho U(\theta)^\dagger O)\ge b\}$. Their VC dimension satisfies
--
--   $$\operatorname{VCdim}\{h_\theta\}\le\sum_{m=0}^{\lfloor n/2\rfloor}(n-2m+1)^2=\binom{n+3}{3}.$$
--
--   The bound is independent of depth and is of order $n^3$. It uses the fixed real Hermitian input commutant feature space; the defective output-commutant statement for arbitrary channels in Theorem 8 is not needed.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 32, Theorem 7 (VC dimension for the unitary Sn model)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.32, Theorem 7: arbitrary mixed-state domain; real Hermitian
commutant dimension, without an extra factor of two. -/
theorem unitaryModel_vcDimension {n L : ℕ} (hn : 2 ≤ n) (word : Fin L → Fin 3)
    (O : QnnOperator n) (hO : O ∈ qnnMeasurementFamily n) (hHerm : O.IsHermitian) (b : ℝ) :
    QAlgorithms.Learning.vcDimSet (classifierFamily word O b) ≤
      ((∑ m : Sector n, blockDim n m ^ 2 : ℕ) : ℕ∞) ∧
    (∑ m : Sector n, blockDim n m ^ 2) = (n + 3).choose 3 := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
