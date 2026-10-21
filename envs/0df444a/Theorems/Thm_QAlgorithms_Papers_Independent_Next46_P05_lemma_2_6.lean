-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_2_6
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_2_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:45:37.464622+00:00
-- url     : https://prove2.me/theorems/c3492b2a-4ca7-4e39-aa6a-ef7e3b63388c
-- title:
--   Lemma 2.6: tube type and nonzero three-gradings
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Tube type means that the restricted root system of a maximal abelian subspace of the noncompact part of a Cartan decomposition has type $C_r$. Then
--
--   $$\mathfrak g\text{ is of tube type}\quad\Longleftrightarrow\quad\exists\,0
--   e h\in\mathfrak g:\ \mathfrak g=\mathfrak g_{-1}(h)\oplus\mathfrak g_0(h)\oplus\mathfrak g_1(h).$$
--
--   Here $\mathfrak g_\lambda(h)=\ker(\operatorname{ad}h-\lambda\operatorname{id})$, and the sums are independent internal sums. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 6, Lemma 2.6

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

/-- Lemma 2.6, PDF pp. 6–7. Tube type uses restricted roots and h is nonzero. -/
theorem lemma_2_6 (hg : HermitianSimple (G := G)) :
    RestrictedTubeType (G := G) ↔ ∃ h : G, h ≠ 0 ∧ ThreeGrading h := by sorry

end LieStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
