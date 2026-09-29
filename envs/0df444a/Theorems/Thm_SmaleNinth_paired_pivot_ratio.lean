-- Prove2me | Theorems.Thm_SmaleNinth_paired_pivot_ratio
-- name    : SmaleNinth.paired_pivot_ratio
-- status  : Open
-- author  : @WillR
-- created : 2026-09-24T12:47:14.46995+00:00
-- url     : https://prove2.me/theorems/054fce44-2d1e-4d65-9c3f-9d4b463c23a1
-- title:
--   Ratio invariant for a paired 5-by-5 complementary pivot
-- statement:
--   Let $S$ be a $5\\times5$ real skew-symmetric matrix. Add its last row to its first row, perform a Gauss-Jordan pivot at position $(1,1)$, and then perform the complementary pivot at position $(4,4)$, with the three displayed pivot denominators nonzero. In the resulting matrix, the $(5,5)$ entry is zero and the two off-diagonal ratios in the last row and last column are equal. More explicitly, if $a=S_{1,4}$ and $d=S_{4,4}-a$, then the cross-multiplied identities are $a(S_2)_{2,5}=d(S_2)_{5,2}$ and $a(S_2)_{3,5}=d(S_2)_{5,3}$. The conclusion is deliberately stated without dividing by potentially zero entries; it is the algebraic base invariant used to justify the complementary-pivot route.
-- source:
--   Samuel Awoniyi, *On pairs of complementary GJ pivotings transforming skew-symmetric matrices*, arXiv:2410.19350v1, Section 2, Lemma 1, https://arxiv.org/abs/2410.19350

import Definitions.Def_SmaleNinth_GaussJordanPivot
import Mathlib.Tactic

open Matrix SmaleNinth

namespace SmaleNinth

theorem paired_pivot_ratio (S : Matrix (Fin 5) (Fin 5) ℝ)
    (hS : S.transpose = -S)
    (hq : S 0 4 ≠ 0)
    (ha : S 0 3 ≠ 0)
    (hd : S 3 4 - S 0 3 ≠ 0) :
    (pairedPivot5 S) 4 4 = 0 ∧
      S 0 3 * (pairedPivot5 S) 1 4 =
        (S 3 4 - S 0 3) * (pairedPivot5 S) 4 1 ∧
      S 0 3 * (pairedPivot5 S) 2 4 =
        (S 3 4 - S 0 3) * (pairedPivot5 S) 4 2 := by sorry

end SmaleNinth
