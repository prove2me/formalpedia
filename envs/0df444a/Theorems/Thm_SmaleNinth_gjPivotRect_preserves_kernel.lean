-- Prove2me | Theorems.Thm_SmaleNinth_gjPivotRect_preserves_kernel
-- name    : SmaleNinth.gjPivotRect_preserves_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T07:29:09.764768+00:00
-- url     : https://prove2.me/theorems/930712f8-a37b-4149-878d-9c5586292a76
-- title:
--   Kernel preservation under a rectangular Gauss-Jordan pivot
-- statement:
--   Let $S$ be a rectangular real matrix, let $(i,j)$ be a row-column position, and assume that the pivot $S_{ij}$ is nonzero. A rectangular Gauss--Jordan pivot normalizes row $i$ and subtracts the corresponding multiple of that row from every other row. This operation preserves the homogeneous solution set: the original system $Sz=0$ has only the zero solution exactly when the pivoted system $(S')z=0$ has only the zero solution.
--
--   The statement is the elementary algebraic invariant behind the complementary pivoting route of Samuel Awoniyi, *A strongly polynomial-time algorithm for the general linear programming problem*, arXiv:2503.12041v10, Sections 4, 6, and 7. It does not assert a termination bound for the complete real-RAM algorithm.
-- source:
--   Samuel Awoniyi, *A strongly polynomial-time algorithm for the general linear programming problem*, arXiv:2503.12041v10, Sections 4, 6, and 7, https://arxiv.org/abs/2503.12041

import Definitions.Def_SmaleNinth_GaussJordanPlus
import Mathlib.Tactic

open Matrix

theorem SmaleNinth.gjPivotRect_preserves_kernel {r c : ℕ}
    (S : Matrix (Fin r) (Fin c) ℝ) (i : Fin r) (j : Fin c) (hp : S i j ≠ 0) :
    (∀ z : Fin c → ℝ, S.mulVec z = 0) ↔
      ∀ z : Fin c → ℝ, (SmaleNinth.gjPivotRect S i j).mulVec z = 0 := by sorry
