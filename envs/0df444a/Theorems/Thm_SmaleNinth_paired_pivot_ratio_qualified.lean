-- Prove2me | Theorems.Thm_SmaleNinth_paired_pivot_ratio_qualified
-- name    : SmaleNinth.paired_pivot_ratio_qualified
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T12:53:38.658892+00:00
-- url     : https://prove2.me/theorems/4ca4db23-5040-46ac-acdb-610cb8cb86f0
-- title:
--   Ratio invariant for a paired 5-by-5 complementary pivot (qualified interface)
-- statement:
--   Let $S$ be a $5\times5$ real skew-symmetric matrix. Add its last row to its first row, perform a Gauss-Jordan pivot at position $(1,1)$, and then perform the complementary pivot at position $(4,4)$, with the three displayed pivot denominators nonzero. In the resulting matrix, the $(5,5)$ entry is zero and the two off-diagonal ratios in the last row and last column are equal. The cross-multiplied identities avoid division by potentially zero entries. This is the fixed 5-by-5 base invariant from arXiv:2410.19350v1, Lemma 1.
-- source:
--   Samuel Awoniyi, *On pairs of complementary GJ pivotings transforming skew-symmetric matrices*, arXiv:2410.19350v1, Section 2, Lemma 1, https://arxiv.org/abs/2410.19350

import Definitions.Def_SmaleNinth_GaussJordanPivot
import Mathlib.Tactic

open Matrix

namespace SmaleNinth

theorem paired_pivot_ratio_qualified (S : Matrix (Fin 5) (Fin 5) ℝ)
    (hS : S.transpose = -S)
    (hq : S 0 4 ≠ 0)
    (ha : S 0 3 ≠ 0)
    (hd : S 3 4 - S 0 3 ≠ 0) :
    (SmaleNinth.pairedPivot5 S) 4 4 = 0 ∧
      S 0 3 * (SmaleNinth.pairedPivot5 S) 1 4 =
        (S 3 4 - S 0 3) * (SmaleNinth.pairedPivot5 S) 4 1 ∧
      S 0 3 * (SmaleNinth.pairedPivot5 S) 2 4 =
        (S 3 4 - S 0 3) * (SmaleNinth.pairedPivot5 S) 4 2 := by sorry

end SmaleNinth
