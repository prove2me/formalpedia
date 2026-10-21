-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_solvable_complement_compact
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.solvable_complement_compact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:45:08.169064+00:00
-- url     : https://prove2.me/theorems/4c2e74d1-a019-46c8-90f8-93e81f595b04
-- title:
--   Lemma 2.23
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional real solvable admissible Lie algebra, $\mathfrak u$ its maximal nilpotent ideal, and $\mathfrak a$ a given abelian subalgebra with $\mathfrak g=\mathfrak u\rtimes\mathfrak a$. Then
--   $$\mathfrak a\text{ is compactly embedded in }\mathfrak g,\qquad \mathfrak z(\mathfrak g)+\mathfrak a\text{ is a compactly embedded Cartan subalgebra}.$$
--   The sum is the actual subspace sum with the ambient bracket. This controls every specified abelian complement.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 12, Lemma 2.23

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

/-- Lemma 2.23, PDF p. 12: the GIVEN abelian complement is compactly embedded. -/
theorem solvable_complement_compact [LieAlgebra.IsSolvable G]
    (ha : LieAdmissible (G := G)) (U : LieIdeal ℝ G) (hu : MaximalNilpotent U)
    (A : LieSubalgebra ℝ G) (hab : ∀ a b : A, ⁅a, b⁆ = 0) (hc : Complement U A) :
    CompactlyEmbedded (A : Set G) ∧
    ∃ T : LieSubalgebra ℝ G,
      T.toSubmodule = (LieAlgebra.center ℝ G).toSubmodule ⊔ A.toSubmodule ∧
      CompactCartan T := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
