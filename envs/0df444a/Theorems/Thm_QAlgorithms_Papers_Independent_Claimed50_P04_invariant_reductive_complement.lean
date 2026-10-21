-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_invariant_reductive_complement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.invariant_reductive_complement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:48:04.974271+00:00
-- url     : https://prove2.me/theorems/60a12fba-cc4a-4745-8d5a-dc9245d971f7
-- title:
--   Theorem 2.27
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional real admissible Lie algebra, $\mathfrak u$ its maximal nilpotent ideal, and $D$ a derivation with $\mathfrak g=\mathfrak g_{-1}(D)\oplus\mathfrak g_0(D)\oplus\mathfrak g_1(D)$. There exists a reductive quasihermitian subalgebra $\mathfrak l$ such that
--   $$\mathfrak g=\mathfrak u\rtimes\mathfrak l,\qquad D(\mathfrak l)\subseteq\mathfrak l,\qquad D(\mathfrak z(\mathfrak l))=0.$$
--   All complement data are conclusions. This adapts a structural splitting to the given derivation.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 13, Theorem 2.27

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

/-- Theorem 2.27, PDF pp. 13–14. The complement, its invariance, and D(z(l))=0
are conclusions; no appendix algebraic-group hypothesis is added. -/
theorem invariant_reductive_complement (ha : LieAdmissible (G := G))
    (U : LieIdeal ℝ G) (hu : MaximalNilpotent U) (D : LieDerivation ℝ G G)
    (hd : ThreeGraded D.toLinearMap) :
    ∃ L : LieSubalgebra ℝ G, Complement U L ∧
      LieAlgebra.HasCentralRadical ℝ L ∧ Quasihermitian (G := L) ∧
      (∀ x : L, D (x : G) ∈ L) ∧
      (∀ x : LieAlgebra.center ℝ L, D ((x : L) : G) = 0) := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
