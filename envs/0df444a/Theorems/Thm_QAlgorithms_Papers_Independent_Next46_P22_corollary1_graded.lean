-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_corollary1_graded
-- name    : QAlgorithms.Papers.Independent.Next46.P22.corollary1_graded
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:40:21.584984+00:00
-- url     : https://prove2.me/theorems/2eb11a60-ee95-4541-bf85-3b6f8f4906a4
-- title:
--   Corollary to Theorem 1 (graded radicals)
-- statement:
--   Let $F$ have characteristic zero, $G$ be a finite group and $L=\bigoplus_g L^{(g)}$ a finite-dimensional $G$-graded $F$-Lie algebra. Its solvable radical $R$ and nilpotent radical $N$ are both graded:
--
--   $$R=\bigoplus_g(R\cap L^{(g)}),\qquad N=\bigoplus_g(N\cap L^{(g)}).$$
--
--   The field need not be algebraically closed, and the group need not be abelian. The finite-group hypothesis is retained for both radical conclusions.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 6, Corollary to Theorem 1 (graded radicals)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Graded corollary to Theorem 1, PDF p.6: finite G; F need not be closed. -/
theorem corollary1_graded [CharZero F] [FiniteDimensional F L]
    {G : Type*} [Group G] [Finite G] (D : Grading F G L) (hD : GradedLie D) :
    GradedSubspace D (LieAlgebra.radical F L).toSubmodule ∧
    GradedSubspace D (lieNilpotentRadical F L).toSubmodule := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
