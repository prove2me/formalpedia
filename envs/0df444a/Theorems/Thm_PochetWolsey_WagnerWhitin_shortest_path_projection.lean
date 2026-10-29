-- Prove2me | Theorems.Thm_PochetWolsey_WagnerWhitin_shortest_path_projection
-- name    : PochetWolsey.WagnerWhitin.shortest_path_projection
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:27.216203+00:00
-- url     : https://prove2.me/theorems/4d47143b-6683-40a2-958f-0a74ffb3b453
-- title:
--   Theorem 7.9 — shortest-path projection equals the LS-U hull projection
-- statement:
--   Let $n\ge1$, $d_t\ge0$, and $M>0$ with $M\ge\sum_t d_t$. Then
--   $$\operatorname{proj}_{x,y}Q^{SP-U}=\operatorname{proj}_{x,y}\operatorname{conv}(X^{LS-U}).$$
--   Both projections eliminate the auxiliary coordinates existentially. The convex hull is taken in the full $(x,y,s)$ space before stock is eliminated on the right.
--
--   This identifies the complete projected feasible region, independently of any cost vector.
--
--   **Formalization Note** Production nonnegativity uses the book's production convention and (7.47), with the printed defect in (7.4) recorded in F1. End stocks are zero and the finite big-$M$ bound is explicitly nonbinding.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 224 (PDF 238), Theorem 7.9

import Mathlib
import Definitions.Def_PochetWolsey_WagnerWhitin_ShortestPath

open scoped BigOperators

namespace PochetWolsey.WagnerWhitin

theorem shortest_path_projection (n : ℕ) (hn : 0 < n)
    (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (M : ℝ) (hMpos : 0 < M) (hM : (∑ t, d t) ≤ M) :
    spProject d = projectXY (convexHull ℝ (lsFeasible d M)) := by sorry

end PochetWolsey.WagnerWhitin
