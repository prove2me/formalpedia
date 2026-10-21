-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_theorem_3_9
-- name    : QAlgorithms.Papers.Independent.Next46.P05.theorem_3_9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:57:01.172531+00:00
-- url     : https://prove2.me/theorems/1dc1de08-c1da-41cc-9508-31d33119ea64
-- title:
--   Theorem 3.9: full hyperbolic reduction of the cone-span algebra
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. For hyperbolic $h$, set $W_\pm(h)=(\pm W_{\min})\cap\mathfrak g_{\pm1}(h)$ and $\mathfrak s_\pm(h)=\operatorname{span}_{\mathbb R}W_\pm(h)$. Let $\mathfrak s(h)$ be their generated algebra. If it is nonzero, it is hermitian simple of tube type and equals the independent sum $\mathfrak s_-(h)\oplus[\mathfrak s_-(h),\mathfrak s_+(h)]\oplus\mathfrak s_+(h)$. There exists $h_0\in\mathfrak s(h)$ such that
--
--   $$h-h_0\in\mathfrak z_{\mathfrak g}(\mathfrak s(h)),\qquad
--   \mathfrak s(h)=\mathfrak s(h_0)=\mathfrak g_{-1}(h_0)\oplus[\mathfrak g_{-1}(h_0),\mathfrak g_1(h_0)]\oplus\mathfrak g_1(h_0),$$
--
--   and $h_0$ is hyperbolic with ambient complex adjoint spectrum contained in $\{0,\pm\frac12,\pm1\}$. Here $\mathfrak s(h_0)$ is recomputed using the same $W_{\min}$. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 21, Theorem 3.9

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

section LieStatements

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Theorem 3.9, PDF pp. 21–23. The element h0 centralizes the WHOLE s(h) after subtraction;
s(h0) is recomputed, and the conclusion includes simplicity and the direct-sum formula. -/
theorem theorem_3_9 (hg : HermitianSimple (G := G)) (Wmin : Set G)
    (hm : MinimalCone Wmin) (h : G) (hh : Hyperbolic h)
    (hn : sliceAlgebra Wmin h ≠ ⊥) :
    HermitianSimple (G := sliceAlgebra Wmin h) ∧ RestrictedTubeType (G := sliceAlgebra Wmin h) ∧
    DirectThree (sliceAlgebra Wmin h).toSubmodule
      (Submodule.span ℝ (coneSlice Wmin h (-1)))
      (bracketSpan (Submodule.span ℝ (coneSlice Wmin h (-1)))
        (Submodule.span ℝ (coneSlice Wmin h 1)))
      (Submodule.span ℝ (coneSlice Wmin h 1)) ∧
    ∃ h0 : G, h0 ∈ sliceAlgebra Wmin h ∧
      (∀ x ∈ sliceAlgebra Wmin h, ⁅h - h0, x⁆ = 0) ∧
      sliceAlgebra Wmin h = sliceAlgebra Wmin h0 ∧
      DirectThree (sliceAlgebra Wmin h).toSubmodule (adSpace h0 (-1))
        (bracketSpan (adSpace h0 (-1)) (adSpace h0 1)) (adSpace h0 1) ∧
      Hyperbolic h0 ∧ complexSpectrum (LieAlgebra.ad ℝ G h0) ⊆ fiveSpectrum := by sorry

end LieStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
