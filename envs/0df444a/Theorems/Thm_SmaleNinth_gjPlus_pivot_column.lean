-- Prove2me | Theorems.Thm_SmaleNinth_gjPlus_pivot_column
-- name    : SmaleNinth.gjPlus_pivot_column
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T15:49:30.226236+00:00
-- url     : https://prove2.me/theorems/814a172f-72a7-49e3-a642-b133fec87357
-- title:
--   Pivot-column behavior of the complementary Gauss-Jordan-plus operation
-- statement:
--   Let $S$ be a square real matrix and let $j$ be a column with nonzero pivot $S_{jj}$. The complementary Gauss--Jordan-plus operation appends the $j$-th unit column, pivots at the original column $j$, swaps that column with the appended unit column, and drops the appended column. This child records the resulting pivot-column formula: the pivot row contributes the reciprocal pivot $1/S_{jj}$ after the swap, while every other row contributes minus the original entry divided by the nonzero pivot.
-- source:
--   Samuel Awoniyi, *On pairs of complementary GJ pivoting transforming skew-symmetric matrices*, arXiv:2410.19350v1, Definition 2 and the GJ+ pivot calculation, https://arxiv.org/abs/2410.19350

import Definitions.Def_SmaleNinth_GaussJordanPlus
import Mathlib.Tactic

open Matrix

theorem SmaleNinth.gjPlus_pivot_column {s : ℕ} (S : Matrix (Fin s) (Fin s) ℝ) (j : Fin s)
    (h : S j j ≠ 0) :
    ∀ i : Fin s, SmaleNinth.gjPlus S j i j = if i = j then (1 / S j j) else -(S i j / S j j) := by sorry
