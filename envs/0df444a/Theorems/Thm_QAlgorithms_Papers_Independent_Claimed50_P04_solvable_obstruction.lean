-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_solvable_obstruction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.solvable_obstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:50:24.094059+00:00
-- url     : https://prove2.me/theorems/0046146e-b280-4b7d-9c23-f7e8c65ed158
-- title:
--   Theorem 3.9: obstruction for solvable Lie algebras
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional real solvable admissible Lie algebra with $\mathfrak z(\mathfrak g)\subseteq[\mathfrak g,\mathfrak g]$. Let $W$ be a generating invariant closed convex cone whose lineality is central. There is no nonzero derivation $D$ such that
--   $$\mathfrak g=\mathfrak g_{-1}(D)\oplus\mathfrak g_0(D)\oplus\mathfrak g_1(D),\qquad \operatorname{span}(W\cap\mathfrak g_\lambda(D))=\mathfrak g_\lambda(D)\quad(\lambda=\pm1).$$
--   Both signs must hold for the same derivation and cone. This is the solvable obstruction with its essential derived-center condition.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 18, Theorem 3.9: obstruction for solvable Lie algebras

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

/-- Theorem 3.9, PDF pp. 18–19. Central-derived assumption and BOTH signs are retained. -/
theorem solvable_obstruction [LieAlgebra.IsSolvable G]
    (ha : LieAdmissible (G := G))
    (hcenter : LieAlgebra.center ℝ G ≤ LieAlgebra.derivedSeries ℝ G 1)
    (W : Set G) (hw : GeneratingCone W)
    (hline : Lineality W ⊆ LieAlgebra.center ℝ G) :
    ¬ ∃ D : LieDerivation ℝ G G, D ≠ 0 ∧ ThreeGraded D.toLinearMap ∧
      ∀ lam : ℝ, (lam = -1 ∨ lam = 1) →
        Submodule.span ℝ (W ∩ (Module.End.eigenspace D.toLinearMap lam : Set G)) =
          Module.End.eigenspace D.toLinearMap lam := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
