-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_modifiedHookWalk
-- name    : QAlgorithms.Papers.Independent.Next46.P26.modifiedHookWalk
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:11:04.840478+00:00
-- url     : https://prove2.me/theorems/a0eef0b9-051d-4231-a701-5a6328e1a5c5
-- title:
--   Terminal corner law of the modified weighted hook walk
-- statement:
--   Let $\lambda$ be a nonempty Young diagram with positive occupied-row weights $x_i$ and occupied-column weights $y_j$, and put $W=\sum_{(p,q)\in[\lambda]}x_py_q$. Start at $(i,j)$ with mass $x_iy_j/W$. At each step let $(r_1,s_1)$ be the corner of least row $r_1\ge i$ and $(r_2,s_2)$ the corner of least column $s_2\ge j$. Move among $(k,j)$ with $r_1<k\le\lambda'_j$ and $(i,l)$ with $s_2<l\le\lambda_i$, using the row and column weights normalized together. When the modified hook is empty, identify the terminal equal-row/equal-column block with its southeast corner, as in the source’s staircase reduction.
--
--   Let $c$ be the number of corners. Let $U_1,\ldots,U_c$ be the consecutive row blocks of equal row length and $V_1,\ldots,V_c$ the consecutive column blocks of equal column length, ordered by increasing coordinates. Set $X_i=\sum_{k\in U_i}x_k$ and $Y_j=\sum_{l\in V_j}y_l$. Number corners from top right to bottom left. For corner rank $r$, set $s=c+1-r$. Then
--   $$
--   \Pr(\text{terminal corner has rank }r)=\frac{X_rY_s}{W}
--   \prod_{i=1}^{r-1}\left(1+\frac{X_i}{\sum_{k=i+1}^rX_k+\sum_{l=s+1}^{c+1-i}Y_l}\right)
--   \prod_{j=1}^{s-1}\left(1+\frac{Y_j}{\sum_{k=r+1}^{c+1-j}X_k+\sum_{l=j+1}^{s}Y_l}\right).
--   $$
--   This is the law of the modified process on the original diagram, using its reduction to a weighted staircase walk.
-- source:
--   The weighted hook length formula, arXiv:1006.0043v1, PDF p. 9, Theorem 5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 5, p.9: law of the modified walk on the original diagram.
The output identifies the terminal block with its actual corner as in the
staircase proof. The corner rank r is zero-based here, s=c-1-r; positivity and actual
corner membership ensure the subtractions have their intended values. -/
theorem modifiedHookWalk (lam : YoungDiagram) (hne : lam.cells.Nonempty)
    (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y) (z : Cell) (hz : z ∈ corners lam) :
    modifiedTerminalProb lam x y z =
      staircaseWeight (corners lam).card (blockX lam x) (blockY lam y)
        (cornerRank lam z) ((corners lam).card - 1 - cornerRank lam z) /
      totalWeight lam x y := by sorry

end QAlgorithms.Papers.Independent.Next46.P26

end
