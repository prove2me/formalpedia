-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_3_2
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_3_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:52:10.740408+00:00
-- url     : https://prove2.me/theorems/261eaa6b-8464-4e2f-ab6a-40a1c8091891
-- title:
--   Lemma 3.2: one global sign for both cone slices
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $W$ be any pointed generating invariant closed convex cone and $h\in\mathfrak g$. Define $W_\pm(h)=(\pm W)\cap\mathfrak g_{\pm1}(h)$. A single global sign $\varepsilon\in\{1,-1\}$ satisfies
--
--   $$W_+(h)=\varepsilon(W_{\min})_+(h),\qquad W_-(h)=\varepsilon(W_{\min})_-(h).$$
--
--   There is no involution hypothesis and no requirement that $h$ be hyperbolic. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 18, Lemma 3.2

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

/-- Lemma 3.2, PDF p. 18. One sign is chosen for BOTH slices; no tau or hyperbolicity. -/
theorem lemma_3_2 (hg : HermitianSimple (G := G)) (Wmin W : Set G)
    (hm : MinimalCone Wmin) (hw : GeneratingInvariantCone W) (h : G) :
    (coneSlice W h (-1) = coneSlice Wmin h (-1) ∧
      coneSlice W h 1 = coneSlice Wmin h 1) ∨
    (coneSlice W h (-1) = Neg.neg '' coneSlice Wmin h (-1) ∧
      coneSlice W h 1 = Neg.neg '' coneSlice Wmin h 1) := by sorry

end LieStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
