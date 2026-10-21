-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_derived_spindler_coordinates
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.derived_spindler_coordinates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:53:57.760473+00:00
-- url     : https://prove2.me/theorems/f8fcaf63-cc6a-4ddb-8222-78633f8a19b6
-- title:
--   Remark 2.13: derived algebra in Spindler coordinates
-- statement:
--   Let $\mathfrak g=\mathfrak g(\mathfrak l,V,Z,\beta)$ be a finite-dimensional real admissible Lie algebra with its structural central coordinate $Z=\mathfrak z(\mathfrak g)$ and $V\ne0$. Put $\mathfrak s=[\mathfrak l,\mathfrak l]$. Its radical is $V\oplus Z\oplus\mathfrak z(\mathfrak l)$, $\mathfrak s$ is a semisimple Levi complement, $V=\operatorname{span}(\mathfrak l.V)$, and
--   $$[\mathfrak g,\mathfrak g]=V\oplus[V,V]\oplus\mathfrak s.$$
--   All spaces and brackets are those of the original presentation, giving the derived algebra the corresponding Spindler bracket. This identifies the perfect part.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 8, Remark 2.13: derived algebra in Spindler coordinates

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

/-- Remark 2.13, PDF p. 8. Includes the radical, Levi complement, effective module span,
and derived algebra in the specified coordinates. Nonzero V is retained. -/
theorem derived_spindler_coordinates (ha : LieAdmissible (G := G))
    (P : SpindlerPresentation (G := G)) (hv : P.V ≠ ⊥) :
    (LieAlgebra.radical ℝ G).toSubmodule = P.V ⊔ (LieAlgebra.center ℝ G).toSubmodule ⊔
      ((LieAlgebra.center ℝ P.L).toSubmodule.map P.L.incl.toLinearMap) ∧
    LieAlgebra.IsSemisimple ℝ (LieAlgebra.derivedSeries ℝ P.L 1) ∧
    IsCompl (LieAlgebra.radical ℝ G).toSubmodule
      ((LieAlgebra.derivedSeries ℝ P.L 1).toSubmodule.map P.L.incl.toLinearMap) ∧
    P.V = bracketSpan P.L.toSubmodule P.V ∧
    (LieAlgebra.derivedSeries ℝ G 1).toSubmodule = P.V ⊔ bracketSpan P.V P.V ⊔
      ((LieAlgebra.derivedSeries ℝ P.L 1).toSubmodule.map P.L.incl.toLinearMap) := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
