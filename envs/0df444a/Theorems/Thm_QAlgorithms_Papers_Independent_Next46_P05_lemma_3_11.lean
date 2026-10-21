-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_3_11
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_3_11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:58:53.625035+00:00
-- url     : https://prove2.me/theorems/781e7c97-3ce0-4395-94ee-1608e8f8c593
-- title:
--   Lemma 3.11: restriction to the extreme tube algebra
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and let $h\in\mathfrak g^\tau$ be hyperbolic with exact complex spectrum $\{0,\pm\frac12,\pm1\}$. Then
--
--   $$\mathfrak g_t(h)=\mathfrak g_{-1}(h)\oplus[\mathfrak g_{-1}(h),\mathfrak g_1(h)]\oplus\mathfrak g_1(h)$$
--
--   is $\tau$-invariant, hermitian simple of tube type, and contains $h$. Its minimal cone can be oriented inside $W_{\min}$. With this orientation, the genuine restriction $\tau|_{\mathfrak g_t(h)}$ satisfies
--
--   $$\mathfrak g(\tau,h)=\mathfrak g_t(h)(\tau|_{\mathfrak g_t(h)},h)$$
--
--   as embedded subalgebras of $\mathfrak g$. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 23, Lemma 3.11

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

/-- Lemma 3.11, PDF p. 23. Exact spectrum, actual restriction, and compatible Wmin(g_t).
All equalities compare embedded algebras, rather than only abstract types. -/
theorem lemma_3_11 (hg : HermitianSimple (G := G)) (Wmin : Set G)
    (hm : MinimalCone Wmin) (tau : G ≃ₗ⁅ℝ⁆ G) (ht : Function.Involutive tau)
    (hr : tau '' Wmin = Neg.neg '' Wmin) (h : G) (hf : tau h = h)
    (hh : Hyperbolic h) (hsp : complexSpectrum (LieAlgebra.ad ℝ G h) = fiveSpectrum) :
    tau '' (tubeAlgebra h : Set G) = (tubeAlgebra h : Set G) ∧
    HermitianSimple (G := tubeAlgebra h) ∧ RestrictedTubeType (G := tubeAlgebra h) ∧
    DirectThree (tubeAlgebra h).toSubmodule (adSpace h (-1))
      (bracketSpan (adSpace h (-1)) (adSpace h 1)) (adSpace h 1) ∧
    ∃ htube : tubeAlgebra h, (htube : G) = h ∧
      ∃ tauT : tubeAlgebra h ≃ₗ⁅ℝ⁆ tubeAlgebra h,
        (∀ x : tubeAlgebra h, (tauT x : G) = tau (x : G)) ∧
        ∃ Wtube : Set (tubeAlgebra h), MinimalCone Wtube ∧
          (∀ x ∈ Wtube, (x : G) ∈ Wmin) ∧
          (causalAlgebra Wmin tau h : Set G) =
            (Subtype.val : tubeAlgebra h → G) '' (causalAlgebra Wtube tauT htube : Set _) := by sorry

end AdditionalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
