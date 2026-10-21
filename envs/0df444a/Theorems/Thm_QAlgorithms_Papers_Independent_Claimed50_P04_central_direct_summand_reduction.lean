-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_central_direct_summand_reduction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.central_direct_summand_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:55:52.916612+00:00
-- url     : https://prove2.me/theorems/56378b40-3675-4048-8328-36084b4506da
-- title:
--   Remark 3.3(a): central direct summand reduction
-- statement:
--   Let $\mathfrak g=\mathfrak g(\mathfrak l,V,Z,\beta)$ be finite-dimensional real admissible with $Z=\mathfrak z(\mathfrak g)$. Let $D$ be a real-diagonalizable derivation preserving $\mathfrak l$ and $V$. Then $Z$ and $Z_1=[V,V]$ are $D$-invariant. There exists a $D$-invariant central complement $Z_2$ with
--   $$Z=Z_1\oplus Z_2,\qquad \mathfrak g=\mathfrak g(\mathfrak l,V,Z_1,\beta)\oplus Z_2.$$
--   The smaller summand is admissible with the restricted ambient bracket. Moreover, $Z_1=Z$ if and only if $\mathfrak z(\mathfrak g)\subseteq[\mathfrak g,\mathfrak g]$. This makes the derived-center reduction explicit.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 16, Remark 3.3(a): central direct summand reduction

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

section FurtherStructure

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Remark 3.3(a), PDF p. 16. The invariant central complement is an existential
conclusion; the smaller summand is an actual ideal with the original bracket. -/
theorem central_direct_summand_reduction (ha : LieAdmissible (G := G))
    (P : SpindlerPresentation (G := G)) (D : LieDerivation ℝ G G)
    (hd : RealDiagonalizable D.toLinearMap)
    (hl : ∀ x : P.L, D (x : G) ∈ P.L)
    (hv : ∀ v : P.V, D (v : G) ∈ P.V) :
    (∀ z : LieAlgebra.center ℝ G, D (z : G) ∈ LieAlgebra.center ℝ G) ∧
    (∀ z ∈ bracketSpan P.V P.V, D z ∈ bracketSpan P.V P.V) ∧
    (∃ Z2 : Submodule ℝ G, Z2 ≤ (LieAlgebra.center ℝ G).toSubmodule ∧
      Disjoint (bracketSpan P.V P.V) Z2 ∧
      bracketSpan P.V P.V ⊔ Z2 = (LieAlgebra.center ℝ G).toSubmodule ∧
      (∀ z ∈ Z2, D z ∈ Z2) ∧
      ∃ N : LieIdeal ℝ G,
        N.toSubmodule = P.V ⊔ bracketSpan P.V P.V ⊔ P.L.toSubmodule ∧
        IsCompl N.toSubmodule Z2 ∧ LieAdmissible (G := N)) ∧
    (bracketSpan P.V P.V = (LieAlgebra.center ℝ G).toSubmodule ↔
      LieAlgebra.center ℝ G ≤ LieAlgebra.derivedSeries ℝ G 1) := by sorry

end FurtherStructure

end

end QAlgorithms.Papers.Independent.Claimed50.P04
