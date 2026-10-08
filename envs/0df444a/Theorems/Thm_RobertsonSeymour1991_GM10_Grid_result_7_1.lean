-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Grid_result_7_1
-- name    : RobertsonSeymour1991.GM10.Grid.result_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:20.095081+00:00
-- url     : https://prove2.me/theorems/e5788249-9b12-42ca-8344-3891f1b9b25a
-- title:
--   (7.1), p. 171 — full row iff full column below boundary order θ
-- statement:
--   Let $\theta\ge2$, let $G$ be the $\theta$-grid, and let $X\subseteq E(G)$. If the number of vertices incident with both an edge in $X$ and an edge outside $X$ is less than $\theta$, then
--
--   $$\bigl(\exists i,\ E(P_i)\subseteq X\bigr)\quad\Longleftrightarrow\quad\bigl(\exists j,\ E(Q_j)\subseteq X\bigr).$$
--
--   This relates the horizontal and vertical obstructions used in the small-set argument.
--
--   **Formalization Note** The bound $\theta\ge2$ is the standing assumption of §7. Row and column indices are $0$-based in Lean. The edge boundary is the corrected incidence reading of the page's type slip; it requires one edge in $X$ and one outside $X$.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 171, (7.1)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Grid_GridHypergraph

namespace RobertsonSeymour1991.GM10.Grid

theorem result_7_1 (θ : ℕ) (hθ : 2 ≤ θ)
    (X : Set (RobertsonSeymour1986.GM5.grid θ).edgeSet)
    (hboundary : (boundary θ X).ncard < θ) :
    (∃ i : Fin θ, rowEdges θ i ⊆ X) ↔ ∃ j : Fin θ, colEdges θ j ⊆ X := by sorry

end RobertsonSeymour1991.GM10.Grid
