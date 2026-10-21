-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_weightedHookWalk
-- name    : QAlgorithms.Papers.Independent.Next46.P26.weightedHookWalk
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:09:55.913665+00:00
-- url     : https://prove2.me/theorems/6f7ff2bd-5f2e-4322-b73e-6c2f6088e6cb
-- title:
--   Terminal corner law of the weighted hook walk
-- statement:
--   Let $\lambda$ be a nonempty Young diagram with strictly positive real weights $x_i$ on its occupied rows and $y_j$ on its occupied columns, and let $W=\sum_{(p,q)\in[\lambda]}x_py_q$. Start at $(i,j)$ with probability $x_iy_j/W$. From a noncorner $(i,j)$, choose among all strict lower-leg cells $(k,j)$ and strict right-arm cells $(i,l)$ together: their masses are $x_k/H_{ij}$ and $y_l/H_{ij}$, where $H_{ij}=\sum_{k=i+1}^{\lambda'_j}x_k+\sum_{l=j+1}^{\lambda_i}y_l$. Stop at the first corner.
--
--   For a corner $(r,s)$ put
--   $$
--   P_{rs}=\frac{x_ry_s}{W}\prod_{i=1}^{r-1}\left(1+\frac{x_i}{\sum_{k=i+1}^r x_k+\sum_{l=s+1}^{\lambda_i}y_l}\right)\prod_{j=1}^{s-1}\left(1+\frac{y_j}{\sum_{k=r+1}^{\lambda'_j}x_k+\sum_{l=j+1}^s y_l}\right).
--   $$
--   The actual stopped process satisfies
--   $$
--   \Pr(\text{terminal cell}=(r,s))=P_{rs}.
--   $$
--   This gives the terminal law of the weighted hook walk. The probability is computed by summing the transition masses of the stopped paths, not supplied as an independent parameter.
-- source:
--   The weighted hook length formula, arXiv:1006.0043v1, PDF p. 8, Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 4, p.8: terminal-corner law for the ordinary weighted hook walk. -/
theorem weightedHookWalk (lam : YoungDiagram) (hne : lam.cells.Nonempty)
    (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y) (c : Cell) (hc : c ∈ corners lam) :
    terminalProb lam (successors lam) x y c =
      cornerWeight lam x y c.1 c.2 / totalWeight lam x y := by sorry

end QAlgorithms.Papers.Independent.Next46.P26

end
