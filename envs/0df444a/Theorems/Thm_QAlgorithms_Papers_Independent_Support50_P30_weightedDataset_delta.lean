-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_weightedDataset_delta
-- name    : QAlgorithms.Papers.Independent.Support50.P30.weightedDataset_delta
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:28:34.973457+00:00
-- url     : https://prove2.me/theorems/2f55080e-43ad-4051-8b70-d60976766ed1
-- title:
--   Proposition 1 (Weighted dataset Delta bound)
-- statement:
--   Let $\rho_1,\ldots,\rho_M$ be density matrices and $c_1,\ldots,c_M$ arbitrary real coefficients, and put $\sigma=\sum_i c_i\rho_i$. Fix orthonormal Schur coordinates and a sector $\lambda$ with multiplicity $m_\lambda$. For unnormalized compressions in the same coordinates,
--
--   $$\Delta\!\left(\sum_{\nu=1}^{m_\lambda}\sigma_\lambda^\nu\right)\le
--   \left(\sum_{i=1}^M |c_i|\sqrt{\Delta\!\left(\sum_{\nu=1}^{m_\lambda}\rho_{i,\lambda}^\nu\right)}\right)^2.$$
--
--   There is one centered statistic outside each multiplicity sum. The empty ensemble gives zero on both sides. A scaling consequence for arbitrary weights would additionally require control of their total absolute weight; the displayed finite inequality needs no such restriction.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 30, Proposition 1 (Weighted dataset Delta bound)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.30, Proposition 1, Eq.(66): one Delta outside each multiplicity sum. -/
theorem weightedDataset_delta {n M : ℕ} (S : SchurFrame n) (m : Sector n)
    (rho : Fin M → QnnDensity n) (c : Fin M → ℝ) :
    centeredDelta (aggregate S m (dataOperator c rho)) ≤
      (∑ i, |c i| * Real.sqrt (centeredDelta (aggregate S m (rho i).val))) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
