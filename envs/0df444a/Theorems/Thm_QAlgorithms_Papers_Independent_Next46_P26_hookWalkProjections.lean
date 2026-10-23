-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_hookWalkProjections
-- name    : QAlgorithms.Papers.Independent.Next46.P26.hookWalkProjections
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:11:35.819839+00:00
-- url     : https://prove2.me/theorems/404271bd-e15e-44a9-abb7-20e67f8220a0
-- title:
--   Conditional law of both hook-walk projections
-- statement:
--   Let $\lambda$ be a nonempty Young diagram with positive occupied-row and occupied-column weights $x_i,y_j$. Run the ordinary weighted hook walk, whose transition at $(i,j)$ assigns masses proportional to $x_k$ on the strict lower leg and $y_l$ on the strict right arm, normalized together, and stops at a corner.
--
--   Let $I,J$ be nonempty finite coordinate sets with $i_1=\min I$, $r=\max I$, $j_1=\min J$, $s=\max J$, and assume $(r,s)$ is an occupied corner. Let the projections of a full stopped path mean the sets of its visited row and column coordinates. Conditional only on starting at $(i_1,j_1)$, one has
--   $$
--   \Pr(\text{row projection}=I,\ \text{column projection}=J\mid\text{start}=(i_1,j_1))
--   =\frac{\prod_{i\in I\setminus\{i_1\}}x_i}{\prod_{i\in I\setminus\{r\}}\left(\sum_{k=i+1}^r x_k+\sum_{l=s+1}^{\lambda_i}y_l\right)}
--   \frac{\prod_{j\in J\setminus\{j_1\}}y_j}{\prod_{j\in J\setminus\{s\}}\left(\sum_{k=r+1}^{\lambda'_j}x_k+\sum_{l=j+1}^s y_l\right)}.
--   $$
--   The conditional law is evaluated by running from that deterministic start. There is no additional conditioning on the endpoint. Singleton projection sets are handled by empty products.
-- source:
--   The weighted hook length formula, arXiv:1006.0043v1, PDF p. 9, Lemma 6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Lemma 6, pp.9–10: law of both projections, conditional only on the start.
The minima are the starting coordinates and the maxima form a terminal corner. -/
theorem hookWalkProjections (lam : YoungDiagram) (hne : lam.cells.Nonempty)
    (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y)
    (I J : Finset ℕ) (i0 j0 r s : ℕ) (hc : (r, s) ∈ corners lam)
    (hi0 : i0 ∈ I) (hr : r ∈ I) (hI : ∀ i ∈ I, i0 ≤ i ∧ i ≤ r)
    (hj0 : j0 ∈ J) (hs : s ∈ J) (hJ : ∀ j ∈ J, j0 ≤ j ∧ j ≤ s) :
    projectionProb lam x y (i0, j0) I J =
      ((∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
      ((∏ j ∈ J.erase j0, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P26

end
