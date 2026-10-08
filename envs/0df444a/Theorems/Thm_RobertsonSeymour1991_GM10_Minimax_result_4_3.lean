-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_4_3
-- name    : RobertsonSeymour1991.GM10.Minimax.result_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:02:19.09817+00:00
-- url     : https://prove2.me/theorems/ba220176-4127-4993-ad85-38399cf748ac
-- title:
--   (4.3), p. 165 — max(β(G), γ(G)) = θ(G) unless γ(G) = 0 and V(G) ≠ ∅
-- statement:
--   Let $G$ be a finite hypergraph, $\beta(G)$ its branch-width, $\gamma(G)$ the maximum size of an edge ($0$ if there are no edges) and $\theta(G)$ its tangle number. Unless $\gamma(G)=0$ and $V(G)\ne\emptyset$,
--
--   $$\max\bigl(\beta(G),\gamma(G)\bigr)=\theta(G).$$
--
--   This is the minimax theorem of Graph Minors X: tangles are exactly the obstructions to branch-decompositions of small width. The exception is genuine: a hypergraph with a vertex and only edges without ends has $\beta=\gamma=0$ but $\theta=1$.
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances. The exception is the hypothesis $\neg(\gamma(G)=0\wedge V(G)\ne\emptyset)$, exactly as in the paper. $\beta(G)=0$ when $|E(G)|\le1$ and $\theta(G)=0$ when there is no tangle, both as the paper defines them.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 165, (4.3)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_BranchDecomposition

namespace RobertsonSeymour1991.GM10.Minimax

/-- (4.3), p. 165: for any hypergraph `G`, `max(β(G), γ(G)) = θ(G)` unless `γ(G) = 0` and `V(G) ≠ ∅`. -/
theorem result_4_3 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E)
    (h : ¬ (G.maxEdgeSize = 0 ∧ Nonempty V)) :
    max (branchWidth G) G.maxEdgeSize = G.tangleNumber := by sorry

end RobertsonSeymour1991.GM10.Minimax
