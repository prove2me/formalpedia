-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_corollary_3_20
-- name    : QAlgorithms.Papers.Independent.Next46.P05.corollary_3_20
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:04:28.308483+00:00
-- url     : https://prove2.me/theorems/7522f4d3-4193-4e5e-b4c0-827bf9f8dda6
-- title:
--   Corollary 3.20: full-rank tube representatives and compatible enlargement
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and $\theta$ a commuting Cartan involution. There exists $h\in\mathfrak g^\tau\cap\mathfrak p$ that is hyperbolic, has adjoint spectrum contained in $\{0,\pm\frac12,\pm1\}$, and whose generated algebra $\mathfrak g_t(h)$ is hermitian simple of tube type, has its independent extreme/bracket/extreme decomposition, and has the same real rank as $\mathfrak g$. If $\mathfrak g$ is tube type, then $\mathfrak g_t(h)=\mathfrak g$.
--
--   Moreover, for every hyperbolic $h_0\in\mathfrak g^\tau\cap\mathfrak p$ with exact spectrum $\{0,\pm\frac12,\pm1\}$, such an $h$ can be chosen with
--
--   $$\mathfrak g_{\pm1}(h_0)\subseteq\mathfrak g_{\pm1}(h),\qquad[h,h_0]=0,\qquad
--   h,h_0\in[\mathfrak g^{-\tau}_{-1}(h),\mathfrak g^{-\tau}_1(h)]\subseteq\mathfrak g_t(h).$$
--
--   The initial existence is independent of the second assertion. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 28, Corollary 3.20

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

/-- Corollary 3.20, PDF p. 28. Unconditional existence is separate from the
stronger choice depending on h0; its antecedent has EXACT five-point spectrum. -/
theorem corollary_3_20 (hg : HermitianSimple (G := G)) (Wmin : Set G)
    (hm : MinimalCone Wmin) (tau theta : G ≃ₗ⁅ℝ⁆ G)
    (hp : CompatiblePair Wmin tau theta) :
    (∃ h : G, FullRankTube tau theta h) ∧
    ∀ h0 : G, tau h0 = h0 → theta h0 = -h0 → Hyperbolic h0 →
      complexSpectrum (LieAlgebra.ad ℝ G h0) = fiveSpectrum →
      ∃ h : G, FullRankTube tau theta h ∧
        adSpace h0 (-1) ≤ adSpace h (-1) ∧ adSpace h0 1 ≤ adSpace h 1 ∧ ⁅h, h0⁆ = 0 ∧
        h ∈ bracketSpan (adSpace h (-1) ⊓ autoSpace tau (-1))
          (adSpace h 1 ⊓ autoSpace tau (-1)) ∧
        h0 ∈ bracketSpan (adSpace h (-1) ⊓ autoSpace tau (-1))
          (adSpace h 1 ⊓ autoSpace tau (-1)) ∧
        bracketSpan (adSpace h (-1) ⊓ autoSpace tau (-1))
          (adSpace h 1 ⊓ autoSpace tau (-1)) ≤ (tubeAlgebra h).toSubmodule := by sorry

end AdditionalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
