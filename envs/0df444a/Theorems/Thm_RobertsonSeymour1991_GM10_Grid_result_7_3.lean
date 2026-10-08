-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Grid_result_7_3
-- name    : RobertsonSeymour1991.GM10.Grid.result_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:26.448705+00:00
-- url     : https://prove2.me/theorems/1885e820-c211-4f31-b1ba-97b71140a104
-- title:
--   (7.3), p. 173 — small-side separations form a grid tangle of order θ
-- statement:
--   Let $\theta\ge2$ and let $G$ be the $\theta$-grid. Let $\mathcal T$ contain exactly the separations $(A,B)$ of $G$ of order less than $\theta$ for which $E(A)$ is small. Then
--
--   $$\mathcal T\text{ is a tangle in $G$ of order }\theta.$$
--
--   Thus every low-order separation is oriented by a small side, no three selected first sides cover $G$, and no selected first side contains all vertices of $G$. The result supplies the grid tangle used later when the paper relates tangles to grid minors.
--
--   **Formalization Note** The paper's §7 fixes $\theta\ge2$. The grid uses the published simple graph on $0$-based coordinate pairs, converted to a finite hypergraph with the same edges. `IsTangle` includes all three axioms, including $V(A)\ne V(G)$; none is omitted.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 173, (7.3)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Grid_GridTangle

namespace RobertsonSeymour1991.GM10.Grid

theorem result_7_3 (θ : ℕ) (hθ : 2 ≤ θ) :
    Hypergraph.IsTangle (gridHypergraph θ) θ (gridTangle θ) := by sorry

end RobertsonSeymour1991.GM10.Grid
