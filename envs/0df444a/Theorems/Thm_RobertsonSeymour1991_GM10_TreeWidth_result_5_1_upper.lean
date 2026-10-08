-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TreeWidth_result_5_1_upper
-- name    : RobertsonSeymour1991.GM10.TreeWidth.result_5_1_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:04:14.726478+00:00
-- url     : https://prove2.me/theorems/beafb2bd-9c33-4a21-815a-0f94b10cb5e8
-- title:
--   (5.1), second inequality, p. 168 — ω(G) + 1 ≤ max(⌊(3/2)β(G)⌋, γ(G), 1)
-- statement:
--   Let $G$ be a finite hypergraph, with branch-width $\beta(G)$, maximum edge size $\gamma(G)$ and tree-width $\omega(G)$. Then
--   $$\omega(G) + 1 \le \max\bigl(\lfloor \tfrac32 \beta(G) \rfloor,\ \gamma(G),\ 1\bigr).$$
--
--   This is the second of the two inequalities of (5.1): a branch-decomposition of small width yields a tree-decomposition of comparable width, so tree-width is bounded by branch-width up to a factor $3/2$ (and the edge-size and non-emptiness corrections).
--
--   **Formalization Note** $\lfloor \tfrac32\beta(G)\rfloor$ is the natural-number floor division `3 * branchWidth G / 2`; both sides are compared in $\mathbb Z$ because $\omega(G) = -1$ when $V(G) = \emptyset$. The statement is for every finite hypergraph, as on the page.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 168, (5.1), second inequality

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_BranchDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_TreeDecomposition

namespace RobertsonSeymour1991.GM10.TreeWidth

/-- (5.1), second inequality, p. 168: `ω(G) + 1 ≤ max(⌊(3/2)β(G)⌋, γ(G), 1)` for every finite
hypergraph `G`; `⌊(3/2)β(G)⌋` is the natural-number floor division `3 * β(G) / 2`. -/
theorem result_5_1_upper {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) :
    treeWidth G + 1 ≤ ((max (3 * branchWidth G / 2) (max G.maxEdgeSize 1) : ℕ) : ℤ) := by sorry

end RobertsonSeymour1991.GM10.TreeWidth
