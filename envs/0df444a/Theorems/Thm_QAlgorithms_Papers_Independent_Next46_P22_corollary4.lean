-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_corollary4
-- name    : QAlgorithms.Papers.Independent.Next46.P22.corollary4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:44:46.755812+00:00
-- url     : https://prove2.me/theorems/5e96e061-3ee8-4c48-9b8d-850103500560
-- title:
--   Corollary to Theorem 4
-- statement:
--   Let $F$ be algebraically closed of characteristic zero, $G$ any group and $L$ a finite-dimensional $G$-graded Lie algebra. Its solvable radical $R$ is graded, and there exists a graded maximal semisimple subalgebra $B$ with
--
--   $$L=B\oplus R$$
--
--   as an internal sum of graded subspaces. Gradedness of $R$ is a conclusion, not an additional hypothesis. This is the closed-field arbitrary-group specialization.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 10, Corollary to Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Corollary to Theorem 4, PDF p.10: over closed F and arbitrary G,
the radical's gradedness is a conclusion. -/
theorem corollary4 [CharZero F] [IsAlgClosed F] [FiniteDimensional F L]
    {G : Type*} [Group G] (D : Grading F G L) (hD : GradedLie D) :
    ∃ B : LieSubalgebra F L, MaximalSemisimple B ∧ GradedSubspace D B.toSubmodule ∧
      GradedSubspace D (LieAlgebra.radical F L).toSubmodule ∧
      IsCompl B.toSubmodule (LieAlgebra.radical F L).toSubmodule := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
