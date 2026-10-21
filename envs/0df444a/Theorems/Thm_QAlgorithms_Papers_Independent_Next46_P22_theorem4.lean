-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem4
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:46:31.421979+00:00
-- url     : https://prove2.me/theorems/5fe448ad-e6cf-414b-a744-a5ce3b779840
-- title:
--   Theorem 4
-- statement:
--   Let $F$ have characteristic zero, $G$ any group and $L$ a finite-dimensional $G$-graded Lie algebra over $F$. Suppose its actual solvable radical $R$ is graded. There exists a graded maximal semisimple subalgebra $B$ such that
--
--   $$L=B\oplus R$$
--
--   as an internal sum of graded subspaces. The group may be infinite or nonabelian; the graded-radical hypothesis is explicit.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 10, Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Theorem 4, PDF p.10: arbitrary G with explicit graded-radical hypothesis. -/
theorem theorem4 [CharZero F] [FiniteDimensional F L]
    {G : Type*} [Group G] (D : Grading F G L) (hD : GradedLie D)
    (hR : GradedSubspace D (LieAlgebra.radical F L).toSubmodule) :
    ∃ B : LieSubalgebra F L, MaximalSemisimple B ∧ GradedSubspace D B.toSubmodule ∧
      IsCompl B.toSubmodule (LieAlgebra.radical F L).toSubmodule := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
