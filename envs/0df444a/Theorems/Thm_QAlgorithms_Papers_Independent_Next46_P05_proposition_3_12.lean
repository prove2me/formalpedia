-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_proposition_3_12
-- name    : QAlgorithms.Papers.Independent.Next46.P05.proposition_3_12
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:59:27.254372+00:00
-- url     : https://prove2.me/theorems/cf1d0d15-7889-41fe-9488-d7b6b3ab247d
-- title:
--   Proposition 3.12: Jordan restriction and unique Lie extension
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Assume tube type, let $\theta$ be Cartan, and let $0
--   e h\in\mathfrak p$ induce the $-1,0,1$ grading. Put $V=\mathfrak g_1(h)$ and give it the product $a\cdot b=\frac12[[a,y],b]$, unit $x$, and scalar product $-B(a,\theta b)$ from the compatible triple $(2h,x,y)$, as in Example 2.23. The following two assertions hold.
--
--   1. For every involutive $\tau$ reversing $W_{\min}$, commuting with $\theta$, and fixing $h$, the restriction $-\tau|_V$ is a Jordan automorphism.
--   2. For every involutive Jordan automorphism $\sigma$ of $V$, there is a unique involutive Lie automorphism $\sigma_{\mathfrak g}$ such that
--
--   $$\sigma_{\mathfrak g}|_V=\sigma,\qquad \theta\sigma_{\mathfrak g}=\sigma_{\mathfrak g}\theta,\qquad \sigma_{\mathfrak g}(h)=h.$$
--
--   The extension in the second assertion extends $\sigma$ itself. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 23, Proposition 3.12

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

section AdditionalStatements

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Proposition 3.12(a),(b), PDF pp. 23–24. The Lie extension extends sigma itself.
Part (b) is not made conditional on the choice of a cone-reversing tau in part (a). -/
theorem proposition_3_12 (hg : HermitianSimple (G := G)) (hb : RestrictedTubeType (G := G))
    (Wmin : Set G) (hm : MinimalCone Wmin) (theta : G ≃ₗ⁅ℝ⁆ G) (ht : Cartan theta)
    (h : G) (hn : h ≠ 0) (hp : theta h = -h) (hd : ThreeGrading h)
    (J : EuclideanJordan (adSpace h 1)) (hj : KKTModel theta h 1 J) :
    (∀ tau : G ≃ₗ⁅ℝ⁆ G, Function.Involutive tau →
      tau '' Wmin = Neg.neg '' Wmin →
      (∀ x, theta (tau x) = tau (theta x)) → tau h = h →
      ∃ a : JordanAuto J, ∀ v : adSpace h 1, (a.linear v : G) = -tau (v : G)) ∧
    (∀ a : JordanAuto J, Function.Involutive a.linear →
      ∃! ext : G ≃ₗ⁅ℝ⁆ G, Function.Involutive ext ∧
        (∀ x, theta (ext x) = ext (theta x)) ∧ ext h = h ∧
        ∀ v : adSpace h 1, ext (v : G) = (a.linear v : G)) := by sorry

end AdditionalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
