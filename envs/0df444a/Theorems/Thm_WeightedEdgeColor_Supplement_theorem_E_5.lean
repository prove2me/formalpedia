-- Prove2me | Theorems.Thm_WeightedEdgeColor_Supplement_theorem_E_5
-- name    : WeightedEdgeColor.Supplement.theorem_E_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:40:51.356107+00:00
-- url     : https://prove2.me/theorems/252b0add-45d2-49ba-b13c-dc0181d7c1a1
-- title:
--   Theorem E.5 — bipartite multigraphs: $\chi'_w(G)\le(5/3+o(1))\,\mathrm{bp}(G)$
-- statement:
--   For every $\varepsilon>0$ there is a constant $C_\varepsilon$ such that every finite bipartite weighted multigraph $G$ with edge weights in $(0,1]$ satisfies
--   $$
--   \chi'_w(G)\le\left(\tfrac53+\varepsilon\right)\mathrm{bp}(G)+C_\varepsilon ,
--   $$
--   that is, $\chi'_w(G)\le(\tfrac53+o(1))\,\mathrm{bp}(G)$. The constant is independent of the number of vertices, the edge multiplicities and the smallest edge weight.
--
--   Here $\chi'_w(G)$ is the least number of colors in a proper weighted coloring (every color class has incident weight at most one at every vertex) and $\mathrm{bp}(G)$ is the local bin-packing number, the largest over vertices $v$ of the least number of unit bins packing the weights of the edges at $v$.
--
--   It improves the harmonic coefficient $h_\infty\approx1.691$ of Theorem E.4 to $5/3$ and is a step towards the $1.62$ bound of Theorem E.10.
--
--   Differences from the source:
--   - encoding: $\chi'_w(G)\le(\tfrac53+o(1))\,X(G)$ (footnote 2, and the theorem's uniformity sentence) → for every $\varepsilon>0$ there is $C_\varepsilon$, chosen before the vertex and edge types and the graph, such that every bipartite multigraph with real weights in $(0,1]$ has a proper weighted coloring $E\to\{0,\dots,k-1\}$ with $k\le(\tfrac53+\varepsilon)X(G)+C_\varepsilon$; reason: footnote 2 (p.2) defines the asymptotic bound this way; a proper coloring with $k$ colors is $\chi'_w(G)\le k$
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Theorem E.5, p.65; footnote 2, p.2

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring
import Definitions.Def_WeightedEdgeColor_WGraph_bp
import Definitions.Def_WeightedEdgeColor_Supplement_IsBipartite

set_option autoImplicit false

namespace WeightedEdgeColor

namespace Supplement

/-- Theorem E.5: every bipartite weighted multigraph satisfies `χ′_w(G) ≤ (5/3 + o(1)) bp(G)`, with
the error independent of the number of vertices, the multiplicities and the smallest edge weight.

Source: Gajjala, Khan, *Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing*,
preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Theorem E.5, p.65; footnote 2, p.2.

**Formalization Note.** 1. `(c₀ + o(1)) bp` is read by footnote 2 (p.2) and the theorem's own uniformity clause: for every
`ε > 0` there is `Cε`, chosen before the vertex and edge types and the graph, with `χ′_w(G) ≤ (c₀
+ ε) bp(G) + Cε` for every bipartite multigraph with real weights in `(0, 1]`; `χ′_w(G) ≤ X` is "a
proper weighted coloring `E → Fin k` with `k ≤ X`". The theorem has no algorithmic clause.
-/
theorem theorem_E_5 (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ,
      ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
        (G : WGraph V E), IsBipartite G →
        ∃ k : ℕ, (k : ℝ) ≤ (5 / 3 + ε) * (G.bp : ℝ) + Cε ∧ ∃ φ : E → Fin k, G.IsProperColoring φ := by sorry

end Supplement

end WeightedEdgeColor
