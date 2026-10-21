-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_proposition_3_18
-- name    : QAlgorithms.Papers.Independent.Next46.P05.proposition_3_18
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:02:36.847976+00:00
-- url     : https://prove2.me/theorems/64d2c070-a679-4251-b83f-cce94edbd9b4
-- title:
--   Proposition 3.18: the two orthogonal spin-factor possibilities
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and $\theta$ a commuting Cartan involution. Let $0
--   e h\in\mathfrak g$ satisfy $\tau h=h$, $\theta h=-h$, and $\mathfrak g=\mathfrak g_{-1}(h)\oplus\mathfrak g_0(h)\oplus\mathfrak g_1(h)$. Assume $\mathfrak g\cong\mathfrak{so}(2,n)$ with $n\in\mathbb N$, $n
--   e2$, and $\mathfrak g^\tau\cong\mathfrak{so}(1,k)\oplus\mathfrak{so}(1,n-k)$ for $1<k<n-1$. Put $V=\mathfrak g_1(h)$ and give it the product $a\cdot b=\frac12[[a,y],b]$, unit $x$, and scalar product $-B(a,\theta b)$ from the compatible triple $(2h,x,y)$, as in Example 2.23. Then, as Jordan algebras,
--
--   $$V^{-\tau}\cong\mathbb R\times\mathbb R^{n-k}\quad\text{or}\quad V^{-\tau}\cong\mathbb R\times\mathbb R^k.$$
--
--   The spin-factor product on $\mathbb R\times\mathbb R^m$ is $(a,u)\cdot(b,v)=(ab+\langle u,v\rangle,av+bu)$. The orthogonal Lie algebras are the real matrix algebras for diagonal signatures. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 26, Proposition 3.18

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

/-- Proposition 3.18, PDF pp. 26–27. These are JORDAN isomorphisms, not vector-space ones. -/
theorem proposition_3_18 (hg : HermitianSimple (G := G)) (Wmin : Set G)
    (hm : MinimalCone Wmin) (tau theta : G ≃ₗ⁅ℝ⁆ G) (hp : CompatiblePair Wmin tau theta)
    (n k : ℕ) (hn : n ≠ 2) (hk : 1 < k ∧ k < n - 1)
    (eg : Nonempty (G ≃ₗ⁅ℝ⁆ OrthogonalReal 2 n))
    (ef : Nonempty (fixedLie tau ≃ₗ⁅ℝ⁆ (OrthogonalReal 1 k × OrthogonalReal 1 (n - k))))
    (h : G) (hz : h ≠ 0) (hf : tau h = h) (ht : theta h = -h) (hd : ThreeGrading h)
    (J : EuclideanJordan (adSpace h 1)) (hj : KKTModel theta h 1 J)
    (a : JordanAuto J) (ha : ∀ v : adSpace h 1, (a.linear v : G) = -tau (v : G)) :
    SpinIsomorphic J (jordanFixed J a) (n - k) ∨
      SpinIsomorphic J (jordanFixed J a) k := by sorry

end FinalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
