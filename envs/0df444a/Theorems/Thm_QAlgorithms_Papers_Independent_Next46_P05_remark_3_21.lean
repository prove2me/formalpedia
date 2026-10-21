-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_remark_3_21
-- name    : QAlgorithms.Papers.Independent.Next46.P05.remark_3_21
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:07:21.849303+00:00
-- url     : https://prove2.me/theorems/529a08e7-02a6-4614-b58c-24604c19a21c
-- title:
--   Remark-3.21: both orthogonal Jordan cases are attainable
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and $\theta$ a commuting Cartan involution. Assume $\mathfrak g\cong\mathfrak{so}(2,n)$ and $\mathfrak g^\tau\cong\mathfrak{so}(1,k)\oplus\mathfrak{so}(1,n-k)$ with $1<k<n-1$. For the same involution $\tau$, both choices in Proposition 3.18 occur: there is a nonzero $h_1\in\mathfrak g^\tau\cap\mathfrak p$ inducing the three-grading with constructed Jordan algebra $V_1=\mathfrak g_1(h_1)$, and likewise an $h_2$ with $V_2=\mathfrak g_1(h_2)$, such that
--
--   $$V_1^{-\tau}\cong\mathbb R\times\mathbb R^{n-k},\qquad V_2^{-\tau}\cong\mathbb R\times\mathbb R^k$$
--
--   as Jordan algebras with their explicit spin-factor products. When $k=n-k$ the two types may coincide. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 28, Remark-3.21

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P05

namespace QAlgorithms.Papers.Independent.Next46.P05

noncomputable section

open Set

open QAlgorithms.Papers.Independent.Frontier30.P26
  (bracketSpan innerWord Invariant ClosedCone GeneratingInvariantCone CompactlyEmbedded)

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedSpace

section FinalStatements

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Remark 3.21, PDF p. 28. BOTH h choices exist for the SAME tau; when k=n-k
these two existence assertions may have the same isomorphism type. -/
theorem remark_3_21 (hg : HermitianSimple (G := G)) (Wmin : Set G)
    (hm : MinimalCone Wmin) (tau theta : G ≃ₗ⁅ℝ⁆ G) (hp : CompatiblePair Wmin tau theta)
    (n k : ℕ) (hk : 1 < k ∧ k < n - 1)
    (eg : Nonempty (G ≃ₗ⁅ℝ⁆ OrthogonalReal 2 n))
    (ef : Nonempty (fixedLie tau ≃ₗ⁅ℝ⁆ (OrthogonalReal 1 k × OrthogonalReal 1 (n - k)))) :
    SpinRealization tau theta (n - k) ∧ SpinRealization tau theta k := by sorry

end FinalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
