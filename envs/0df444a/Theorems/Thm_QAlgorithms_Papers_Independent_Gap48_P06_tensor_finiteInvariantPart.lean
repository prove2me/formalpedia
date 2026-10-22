-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P06_tensor_finiteInvariantPart
-- name    : QAlgorithms.Papers.Independent.Gap48.P06.tensor_finiteInvariantPart
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:06:45.00382+00:00
-- url     : https://prove2.me/theorems/aa3deaa1-b8ae-40fc-b18b-e0d06ff121c2
-- title:
--   Finite-dimensional invariant parts of completed real Hilbert tensors
-- statement:
--   Let $\pi$ and $\rho$ be orthogonal representations of the same abstract group $G$ on real Hilbert spaces $H$ and $K$. Equip the completed Hilbert tensor product $H\widehat\otimes K$ with the diagonal representation. For any representation space $L$, write $L_f$ for the closed linear span of its finite-dimensional invariant subspaces. Then both assertions hold:
--
--   1. If $H$ has no nonzero finite-dimensional invariant subspaces, neither does $H\widehat\otimes K$; in particular $(H\widehat\otimes K)^G=\{0\}$.
--   2. As closed subspaces of the ambient tensor product,
--
--   $$(H\widehat\otimes K)_f=H_f\widehat\otimes K_f.$$
--
--   The tensor on the right denotes its canonical embedded image, equivalently the closed span of elementary tensors from the two finite invariant parts. There is no separability or continuity assumption on the abstract group. This identifies exactly where finite-dimensional invariant vectors can occur in a tensor representation.
-- source:
--   Reflection Positive Stochastic Processes Indexed by Lie Groups, arXiv:1510.07445v3, PDF p. 41, Lemma 5.24

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P06

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped Topology ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P06

/-- Lemma 5.24, PDF pp.41--42: both the vanishing statement, including fixed
vectors, and the equality of the complete finite-dimensional invariant parts.
No topology on the abstract group or separability of either real Hilbert space
is assumed. Equality in (ii) is of embedded CLOSED subspaces. -/
theorem tensor_finiteInvariantPart
    {G H K : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (pi : G →* (H ≃ₗᵢ[ℝ] H)) (rho : G →* (K ≃ₗᵢ[ℝ] K)) :
    (NoFiniteSubrepresentations (fun g v => pi g v) →
      NoFiniteSubrepresentations (realTensorDiagonalAction pi rho) ∧
        ∀ v, (∀ g, realTensorDiagonalAction pi rho g v = v) → v = 0) ∧
    finiteInvariantPart (realTensorDiagonalAction pi rho) =
      closedTensorSubspace (finiteInvariantPart (fun g v => pi g v))
        (finiteInvariantPart (fun g v => rho g v)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P06

end
