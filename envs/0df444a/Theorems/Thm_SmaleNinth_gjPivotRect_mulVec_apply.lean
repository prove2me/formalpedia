-- Prove2me | Theorems.Thm_SmaleNinth_gjPivotRect_mulVec_apply
-- name    : SmaleNinth.gjPivotRect_mulVec_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T07:50:30.693448+00:00
-- url     : https://prove2.me/theorems/bdf9824c-f2c8-4d4d-87e7-b3b9116ecc6c
-- title:
--   Pointwise row-sum formula for a rectangular Gauss-Jordan pivot
-- statement:
--   For a rectangular real matrix $S$, let $S'$ be the Gauss--Jordan pivot at row $i$ and column $j$. This child records the exact row-sum formula for $(S'z)_a$. The pivot row is the original row sum divided by $S_{ij}$; every other row sum is the original row sum minus $S_{aj}$ times the pivot-row sum divided by $S_{ij}$.
--
--   This is the reusable finite-sum calculation underneath kernel preservation for the complementary pivoting route of Samuel Awoniyi, *A strongly polynomial-time algorithm for the general linear programming problem*, arXiv:2503.12041v10, Sections 4, 6, and 7.
-- source:
--   Samuel Awoniyi, *A strongly polynomial-time algorithm for the general linear programming problem*, arXiv:2503.12041v10, Sections 4, 6, and 7, https://arxiv.org/abs/2503.12041

import Definitions.Def_SmaleNinth_GaussJordanPlus
import Mathlib.Tactic

open Matrix

theorem SmaleNinth.gjPivotRect_mulVec_apply {r c : ℕ}
    (S : Matrix (Fin r) (Fin c) ℝ) (i : Fin r) (j : Fin c)
    (z : Fin c → ℝ) (a : Fin r) :
    (SmaleNinth.gjPivotRect S i j).mulVec z a =
      if a = i then
        S.mulVec z a / S i j
      else
        S.mulVec z a - S a j * (S.mulVec z i) / S i j := by sorry
