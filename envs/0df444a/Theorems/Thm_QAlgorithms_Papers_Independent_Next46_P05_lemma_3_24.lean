-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_3_24
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_3_24
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:05:31.792644+00:00
-- url     : https://prove2.me/theorems/c32ffd1d-175b-4e2b-a5da-0d569fa184b6
-- title:
--   Lemma 3.24: restricted-to-ambient spectral transfer
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and $\theta$ a commuting Cartan involution. Assume $\mathfrak g$ is not of tube type. Let $h\in\mathfrak p$ give the diagonal decomposition into adjoint eigenspaces of degrees $-1,-1/2,0,1/2,1$, and assume $\operatorname{rank}_{\mathbb R}\mathfrak g_t(h)=\operatorname{rank}_{\mathbb R}\mathfrak g$. Let $h_0\in\mathfrak g_t(h)$ commute with $h$, with exact spectrum $\{0,\pm\frac12,\pm1\}$ for its adjoint on $\mathfrak g_t(h)$. Then
--
--   $$\operatorname{spec}(\operatorname{ad}_{\mathfrak g}h_0)=\{0,\pm\tfrac12,\pm1\},\qquad
--   \mathfrak g_t(h_0)\subseteq\mathfrak g_t(h).$$
--
--   No additional semisimplicity assumption on $h_0$ is imposed. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 29, Lemma 3.24

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

/-- Lemma 3.24, PDF p. 29. Non-tube type is inherited from Section 3.4.
Restricted spectrum in the hypothesis and ambient spectrum in the conclusion are distinct;
no ad-semisimplicity hypothesis is added for h0. -/
theorem lemma_3_24 (hg : HermitianSimple (G := G)) (hnt : ¬ RestrictedTubeType (G := G))
    (Wmin : Set G) (hm : MinimalCone Wmin) (tau theta : G ≃ₗ⁅ℝ⁆ G)
    (hp : CompatiblePair Wmin tau theta) (h : G) (ht : theta h = -h)
    (hd : FiveGrading h) (hr : realRank (G := tubeAlgebra h) = realRank (G := G))
    (h0 : tubeAlgebra h) (hc : ⁅h, (h0 : G)⁆ = 0)
    (hs : complexSpectrum (LieAlgebra.ad ℝ (tubeAlgebra h) h0) = fiveSpectrum) :
    complexSpectrum (LieAlgebra.ad ℝ G (h0 : G)) = fiveSpectrum ∧
      tubeAlgebra (h0 : G) ≤ tubeAlgebra h := by sorry

end AdditionalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
