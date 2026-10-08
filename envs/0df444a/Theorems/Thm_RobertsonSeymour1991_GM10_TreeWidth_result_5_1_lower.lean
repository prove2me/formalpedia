-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TreeWidth_result_5_1_lower
-- name    : RobertsonSeymour1991.GM10.TreeWidth.result_5_1_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:00:34.060668+00:00
-- url     : https://prove2.me/theorems/e960e64f-471c-43b6-aa2e-be079326aa09
-- title:
--   (5.1), first inequality, pp. 168–169 — max(β(G), γ(G)) ≤ ω(G) + 1
-- statement:
--   Let $G$ be a finite hypergraph, with branch-width $\beta(G)$, maximum edge size $\gamma(G)$ and tree-width $\omega(G)$. Then
--   $$\max\bigl(\beta(G), \gamma(G)\bigr) \le \omega(G) + 1.$$
--
--   This is the first of the two inequalities of (5.1): branch-width, and the size of the largest edge, are at most one more than the tree-width.
--
--   **Formalization Note** The comparison is in $\mathbb Z$, since $\omega(G) = -1$ when $V(G) = \emptyset$. The statement is for every finite hypergraph, as on the page.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), pp. 168–169, (5.1), first inequality

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_BranchDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_TreeDecomposition

namespace RobertsonSeymour1991.GM10.TreeWidth

/-- (5.1), first inequality, pp. 168–169: `max(β(G), γ(G)) ≤ ω(G) + 1` for every finite
hypergraph `G`. -/
theorem result_5_1_lower {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) :
    ((max (branchWidth G) G.maxEdgeSize : ℕ) : ℤ) ≤ treeWidth G + 1 := by sorry

end RobertsonSeymour1991.GM10.TreeWidth
