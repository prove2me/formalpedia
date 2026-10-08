-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TreeWidth_result_5_1
-- name    : RobertsonSeymour1991.GM10.TreeWidth.result_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:00:53.646794+00:00
-- url     : https://prove2.me/theorems/832397eb-ff8f-4f55-a2f0-0e46bcdd701d
-- title:
--   (5.1), p. 168 — max(β(G), γ(G)) ≤ ω(G) + 1 ≤ max(⌊(3/2)β(G)⌋, γ(G), 1)
-- statement:
--   Let $G$ be a finite hypergraph. Write $\beta(G)$ for its branch-width, $\gamma(G)$ for the maximum number of ends of an edge (with $\gamma(G) = 0$ if $G$ has no edges) and $\omega(G)$ for its tree-width (with $\omega(G) = -1$ if $G$ has no vertices). Then
--   $$\max\bigl(\beta(G), \gamma(G)\bigr) \;\le\; \omega(G) + 1 \;\le\; \max\bigl(\lfloor \tfrac32 \beta(G) \rfloor,\ \gamma(G),\ 1\bigr).$$
--
--   Branch-width and tree-width are thus equivalent width parameters, within a factor $3/2$. Both extremes occur: for $G = K_n$ with $3 \mid n$ the right-hand bound is attained, and for $K_{n,n}$ minus a perfect matching ($n \ge 4$) the left-hand bound is. Combined with (4.3) ($\max(\beta(G), \gamma(G)) = \theta(G)$ unless $\gamma(G) = 0$ and $V(G) \neq \emptyset$), it gives (5.2), which relates tree-width to the tangle number.
--
--   **Formalization Note** $\lfloor \tfrac32\beta(G)\rfloor$ is the natural-number floor division `3 * branchWidth G / 2`; the ceiling would weaken the statement. All comparisons are in $\mathbb Z$ because $\omega(G)$ can be $-1$. Finiteness of $V(G)$ and $E(G)$ is the paper's standing convention (p. 154).
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 168, (5.1)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_BranchDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_TreeDecomposition

namespace RobertsonSeymour1991.GM10.TreeWidth

/-- (5.1), p. 168: for any (finite) hypergraph `G`,
`max(β(G), γ(G)) ≤ ω(G) + 1 ≤ max(⌊(3/2)β(G)⌋, γ(G), 1)`; `⌊(3/2)β(G)⌋` is `3 * β(G) / 2` in `ℕ`. -/
theorem result_5_1 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) :
    ((max (branchWidth G) G.maxEdgeSize : ℕ) : ℤ) ≤ treeWidth G + 1 ∧
      treeWidth G + 1 ≤ ((max (3 * branchWidth G / 2) (max G.maxEdgeSize 1) : ℕ) : ℤ) := by sorry

end RobertsonSeymour1991.GM10.TreeWidth
