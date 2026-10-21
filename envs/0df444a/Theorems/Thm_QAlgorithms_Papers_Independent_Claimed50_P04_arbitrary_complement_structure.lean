-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_arbitrary_complement_structure
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.arbitrary_complement_structure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:45:47.330342+00:00
-- url     : https://prove2.me/theorems/bb3c48a2-9588-42e0-b273-a00fc420c2f2
-- title:
--   Theorem 2.24
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional real admissible Lie algebra, $\mathfrak u$ its maximal nilpotent ideal, and $\mathfrak l$ any given subalgebra complementary to $\mathfrak u$. Then $\mathfrak l$ is reductive and quasihermitian. For every compactly embedded Cartan subalgebra $\mathfrak t_s$ of $[\mathfrak l,\mathfrak l]$, the actual subspace
--   $$\mathfrak t=\mathfrak z(\mathfrak g)+\mathfrak z(\mathfrak l)+\mathfrak t_s$$
--   is a compactly embedded Cartan subalgebra of $\mathfrak g$. The centers and $\mathfrak t_s$ are embedded in the given ambient algebra. This describes all reductive complements.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 12, Theorem 2.24

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

/-- Theorem 2.24, PDF pp. 12–13: arbitrary complement, every compact Cartan of [l,l]. -/
theorem arbitrary_complement_structure (ha : LieAdmissible (G := G))
    (U : LieIdeal ℝ G) (hu : MaximalNilpotent U)
    (L : LieSubalgebra ℝ G) (hc : Complement U L) :
    LieAlgebra.HasCentralRadical ℝ L ∧ Quasihermitian (G := L) ∧
    ∀ TS : LieSubalgebra ℝ (LieAlgebra.derivedSeries ℝ L 1), CompactCartan TS →
      ∃ T : LieSubalgebra ℝ G,
        T.toSubmodule = (LieAlgebra.center ℝ G).toSubmodule ⊔
          ((LieAlgebra.center ℝ L).toSubmodule.map L.incl.toLinearMap) ⊔
          (Submodule.span ℝ {x : G | ∃ y : TS,
            x = (((y : LieAlgebra.derivedSeries ℝ L 1) : L) : G)}) ∧
        CompactCartan T := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
