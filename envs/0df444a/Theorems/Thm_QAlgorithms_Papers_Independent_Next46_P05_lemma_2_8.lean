-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_2_8
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_2_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:46:46.620274+00:00
-- url     : https://prove2.me/theorems/a3f69669-1166-42be-9fc6-4982bd0e76b1
-- title:
--   Lemma 2.8: simple factors of admissible reductive algebras
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Assume $\mathfrak g$ is reductive and admissible: there exists a generating invariant closed convex subset with trivial translation stabilizer. Then every simple ideal $I\triangleleft\mathfrak g$ satisfies
--
--   $$I\text{ is compact}\quad\text{or}\quad I\text{ is hermitian simple}.$$
--
--   Compactness means relative compactness of the adjoint group of $I$; admissibility is not defined by this conclusion. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 7, Lemma 2.8

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

/-- Lemma 2.8, PDF p. 7. Admissibility remains the source's set-existence condition. -/
theorem lemma_2_8 (hg : LineFreeAdmissible (G := G)) [LieAlgebra.HasCentralRadical ℝ G]
    (I : LieIdeal ℝ G) (hi : LieAlgebra.IsSimple ℝ I) :
    CompactlyEmbedded (Set.univ : Set I) ∨ HermitianSimple (G := I) := by sorry

end LieStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
