-- Prove2me | Theorems.Thm_SmaleNinth_gjPlus_nonpivot_column
-- name    : SmaleNinth.gjPlus_nonpivot_column
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T16:12:46.555825+00:00
-- url     : https://prove2.me/theorems/77cca58d-d25e-4215-aaed-78b4fd12b946
-- title:
--   Non-pivot-column update under the complementary Gauss-Jordan-plus operation
-- statement:
--   Let $S$ be a square real matrix and let $j$ be a column with nonzero pivot $S_{jj}$. For any column $q$ different from $j$, the complementary Gauss--Jordan-plus operation leaves the pivot row equal to the normalized original row and updates every other row by subtracting the original pivot-column entry times the normalized pivot row. This is the non-pivot-column formula for the source paper's rectangular GJ+ operation.
-- source:
--   Samuel Awoniyi, *On pairs of complementary GJ pivoting transforming skew-symmetric matrices*, arXiv:2410.19350v1, Definition 2 and the GJ+ pivot calculation, https://arxiv.org/abs/2410.19350

import Definitions.Def_SmaleNinth_GaussJordanPlus
import Mathlib.Tactic

open Matrix

theorem SmaleNinth.gjPlus_nonpivot_column {s : ℕ} (S : Matrix (Fin s) (Fin s) ℝ) (j : Fin s)
    (h : S j j ≠ 0) {i q : Fin s} (hq : q ≠ j) :
    SmaleNinth.gjPlus S j i q =
      if i = j then S j q / S j j
      else S i q - S i j * (S j q / S j j) := by sorry
