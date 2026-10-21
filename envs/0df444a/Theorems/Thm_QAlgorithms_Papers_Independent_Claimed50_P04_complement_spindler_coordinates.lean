-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_complement_spindler_coordinates
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.complement_spindler_coordinates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:46:19.13298+00:00
-- url     : https://prove2.me/theorems/95bcb817-0df9-4182-a330-9eb1f3577023
-- title:
--   Corollary 2.25
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional real admissible Lie algebra with maximal nilpotent ideal $\mathfrak u$. For any complement $\mathfrak l$ and any compactly embedded Cartan subalgebra $\mathfrak t_l$ of $\mathfrak l$, put $V=[\mathfrak t_l,\mathfrak u]$. Then $V$ is stable under the adjoint action of $\mathfrak l$, $V^{\mathfrak t_l}=0$, and
--   $$\mathfrak g\cong\mathfrak g(\mathfrak l,V,\mathfrak z(\mathfrak g),[\cdot,\cdot]|_{V\times V}).$$
--   The isomorphism is encoded by coordinates reconstructing the original algebra. This obtains Spindler coordinates for a prescribed complement.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 13, Corollary 2.25

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

/-- Corollary 2.25, PDF p. 13. V is CONSTRUCTED as [tl,u], and beta is the restricted
ambient bracket. tl is compactly embedded in the specified l. -/
theorem complement_spindler_coordinates (ha : LieAdmissible (G := G))
    (U : LieIdeal ℝ G) (hu : MaximalNilpotent U)
    (L : LieSubalgebra ℝ G) (hc : Complement U L)
    (TL : LieSubalgebra ℝ L) (ht : CompactCartan TL) :
    ∃ P : SpindlerPresentation (G := G), P.L = L ∧
      P.V = bracketSpan (TL.map L.incl).toSubmodule U.toSubmodule ∧
      ∀ v : P.V, (∀ x : L, x ∈ TL → ⁅(x : G), (v : G)⁆ = 0) → v = 0 := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
