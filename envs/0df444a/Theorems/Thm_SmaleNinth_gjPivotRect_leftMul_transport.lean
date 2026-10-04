-- Prove2me | Theorems.Thm_SmaleNinth_gjPivotRect_leftMul_transport
-- name    : SmaleNinth.gjPivotRect_leftMul_transport
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T10:22:58.95874+00:00
-- url     : https://prove2.me/theorems/a71cdbcb-d54f-453c-ae9c-7ef1ca8baa0a
-- title:
--   Left-kernel transport through a rectangular Gauss-Jordan pivot
-- statement:
--   Let $S$ be a rectangular real matrix with nonzero pivot $S_{ij}$, and let $S'$ be the Gauss--Jordan pivot at row $i$ and column $j$. A left multiplier $y$ transports to a left multiplier for $S'$ by leaving every coordinate other than $i$ unchanged and replacing the pivot-row coordinate by
--
--   $$
--   S_{ij}y_i+\sum_{a\ne i}y_aS_{aj}.
--   $$
--
--   If $y^{\mathsf T}S=0$, the column-$j$ equation makes this new pivot coordinate equal to zero. Hence the other coordinates retain their original signs and a nonnegative left-kernel vector is transported to a nonnegative left-kernel vector. This identity isolates the exact row-operation bookkeeping needed before combining transport with an augmented Farkas certificate in a complementary-pivot algorithm.
-- source:
--   Samuel Awoniyi, *A strongly polynomial-time algorithm for the general linear programming problem*, arXiv:2503.12041v10, Sections 4, 6, and 7, https://arxiv.org/abs/2503.12041; the row-operation identity is the elementary left-multiplier calculation underlying the certificate transport.

import Definitions.Def_SmaleNinth_GaussJordanPlus
import Mathlib.Tactic

open Matrix

theorem SmaleNinth.gjPivotRect_leftMul_transport {r c : ℕ}
    (S : Matrix (Fin r) (Fin c) ℝ) (i : Fin r) (j : Fin c)
    (hp : S i j ≠ 0) (y : Fin r → ℝ) :
    (fun a : Fin r =>
      if a = i then
        S i j * y i + ∑ b ∈ (Finset.univ : Finset (Fin r)).erase i, y b * S b j
      else y a) ᵥ* SmaleNinth.gjPivotRect S i j = y ᵥ* S := by sorry
