-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_remark_3_13
-- name    : QAlgorithms.Papers.Independent.Next46.P05.remark_3_13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:06:30.062501+00:00
-- url     : https://prove2.me/theorems/1bcc38d3-d4ce-41e4-8dd6-a71b01f82c03
-- title:
--   Remark-3.13: commuting grading/Jordan-extension factorization
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and $\theta$ a commuting Cartan involution. Let $0
--   e h\in\mathfrak g$ satisfy $\tau h=h$, $\theta h=-h$, and $\mathfrak g=\mathfrak g_{-1}(h)\oplus\mathfrak g_0(h)\oplus\mathfrak g_1(h)$. Put $V=\mathfrak g_1(h)$ and give it the product $a\cdot b=\frac12[[a,y],b]$, unit $x$, and scalar product $-B(a,\theta b)$ from the compatible triple $(2h,x,y)$, as in Example 2.23. Let $\tau_h=\exp(i\pi\operatorname{ad}h)$, equivalently $\tau_h=1-2(\operatorname{ad}h)^2$ on this grading. There exist an involutive Jordan automorphism $\sigma=-\tau|_V$ and its involutive Lie extension $\sigma_{\mathfrak g}$ fixing $h$ and commuting with $\theta$, such that
--
--   $$\tau=\tau_h\circ\sigma_{\mathfrak g}=\sigma_{\mathfrak g}\circ\tau_h,\qquad\sigma_{\mathfrak g}|_V=\sigma.$$
--
--   The extension has no extra minus sign on its restriction. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 24, Remark-3.13

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

/-- Remark 3.13, PDF p. 24. Both commuting factorizations and the extension's sign. -/
theorem remark_3_13 (hg : HermitianSimple (G := G)) (hb : RestrictedTubeType (G := G))
    (Wmin : Set G) (hm : MinimalCone Wmin) (tau theta : G ≃ₗ⁅ℝ⁆ G)
    (hp : CompatiblePair Wmin tau theta) (h : G) (hn : h ≠ 0)
    (hf : tau h = h) (ht : theta h = -h) (hd : ThreeGrading h)
    (J : EuclideanJordan (adSpace h 1)) (hj : KKTModel theta h 1 J) :
    ∃ a : JordanAuto J, Function.Involutive a.linear ∧
      (∀ v : adSpace h 1, (a.linear v : G) = -tau (v : G)) ∧
      ∃ ext : G ≃ₗ⁅ℝ⁆ G, Function.Involutive ext ∧ ext h = h ∧
        (∀ x, theta (ext x) = ext (theta x)) ∧
        (∀ v : adSpace h 1, ext (v : G) = (a.linear v : G)) ∧
        ∀ x : G, tau x = gradingSign h (ext x) ∧ tau x = ext (gradingSign h x) := by sorry

end AdditionalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
