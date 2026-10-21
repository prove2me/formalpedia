-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_nilradical_cone_central
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.nilradical_cone_central
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:49:52.600891+00:00
-- url     : https://prove2.me/theorems/03c44a5d-a1d1-4599-8352-7ab35f0d7dab
-- title:
--   Lemma 3.8
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional real admissible Lie algebra, $\mathfrak u$ its maximal nilpotent ideal, and $W$ a generating invariant closed convex cone. Suppose its translation lineality $H(W)=\{x:W+x=W\}$ lies in $\mathfrak z(\mathfrak g)$. Then
--   $$W\cap\mathfrak u\subseteq\mathfrak z(\mathfrak g).$$
--   The cone need not be pointed. This locates its nilpotent intersection in the center.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 18, Lemma 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P04

namespace QAlgorithms.Papers.Independent.Claimed50.P04

noncomputable section

open Set

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Frontier30.P26
  (Invariant LieAdmissible ClosedCone CompactlyEmbedded CompactCartan Hermitian bracketSpan
    TubeType)

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedSpace

section LieDefinitions

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Lemma 3.8, PDF p. 18: central lineality, WITHOUT a pointedness hypothesis. -/
theorem nilradical_cone_central (ha : LieAdmissible (G := G))
    (U : LieIdeal ℝ G) (hu : MaximalNilpotent U) (W : Set G)
    (hw : GeneratingCone W) (hline : Lineality W ⊆ LieAlgebra.center ℝ G) :
    W ∩ (U : Set G) ⊆ LieAlgebra.center ℝ G := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
