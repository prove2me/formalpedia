-- Prove2me | Theorems.Thm_WeightedEdgeColor_theorem_1_1_simple_graphs
-- name    : WeightedEdgeColor.theorem_1_1_simple_graphs
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:50:39.705198+00:00
-- url     : https://prove2.me/theorems/7013e03c-8e6f-4b94-8478-5f4474aabf92
-- title:
--   Theorem 1.1 (simple graphs) — weighted Vizing: $\chi'_w(G)\le(1+o(1))\,\mathrm{bp}(G)$
-- statement:
--   For every $\varepsilon>0$ there is a constant $C_\varepsilon$ such that every finite simple graph $G$ with edge weights in $(0,1]$ satisfies
--   $$
--   \chi'_w(G)\le(1+\varepsilon)\,\mathrm{bp}(G)+C_\varepsilon ,
--   $$
--   where $\chi'_w(G)$ is the least number of colors in a proper weighted coloring and $\mathrm{bp}(G)$ is the local bin-packing number. The constant $C_\varepsilon$ is independent of the number of vertices and of the edge weights. In the notation of the paper, $\chi'_w(G)\le(1+o(1))\,\mathrm{bp}(G)$.
--
--   Since $\mathrm{bp}(G)\le\chi'_w(G)$ always, the local bin-packing bound determines the weighted chromatic index of simple graphs up to a $1+o(1)$ factor, whether or not the graph is bipartite: an asymptotic weighted analogue of Vizing's theorem. The coefficient one is optimal, and the additive constant cannot be dropped (a triangle with unit weights has $\mathrm{bp}=2$ and needs three colors).
--
--   **Formalization Note** $C_\varepsilon$ is chosen before the graph. "$\chi'_w(G)\le X$" is "there are $k\le X$ and a proper weighted coloring with $k$ colors". Simple means no parallel edges; loops are excluded by the graph model.
--
--   Differences from the source:
--   - encoding: $\chi'_w(G)\le(1+o(1))\,\mathrm{bp}(G)$ (footnote 2) → for every $\varepsilon>0$ there is $C_\varepsilon$, chosen before the graph, and a proper weighted coloring with $k\le(1+\varepsilon)\mathrm{bp}(G)+C_\varepsilon$ colors; reason: footnote 2 defines the asymptotic bound this way, and a coloring with $k$ colors is $\chi'_w(G)\le k$
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Theorem 1.1 (row "Simple graphs") with footnote 2, p.2; proof Section C.3, p.43

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring
import Definitions.Def_WeightedEdgeColor_WGraph_bp

set_option autoImplicit false

namespace WeightedEdgeColor

/-- Theorem 1.1, row "Simple graphs", with footnote 2: `χ′_w(G) ≤ (1 + o(1)) bp(G)`, i.e. for
every `ε > 0` there is `C_ε` such that every finite simple graph `G` with edge weights in
`(0, 1]` has a proper weighted coloring with at most `(1 + ε) bp(G) + C_ε` colors.

Source: Gajjala, Khan, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Theorem 1.1 (row "Simple graphs") with footnote 2, p.2; proof Section C.3, p.43.

**Formalization Note.** `C_ε` is chosen before the vertex and edge types and the graph, so it
is independent of the number of vertices and of the weights (footnote 2). `χ′_w(G) ≤ X` is "a
proper weighted coloring `E → Fin k` with `k ≤ X`". Simple means no parallel edges
(`Function.Injective G.ends`); loops are excluded by the carrier. -/
theorem theorem_1_1_simple_graphs (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple →
      ∃ k : ℕ, (k : ℝ) ≤ (1 + ε) * (G.bp : ℝ) + Cε ∧ ∃ φ : E → Fin k, G.IsProperColoring φ := by sorry

end WeightedEdgeColor
