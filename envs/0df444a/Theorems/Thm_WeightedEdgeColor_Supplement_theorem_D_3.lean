-- Prove2me | Theorems.Thm_WeightedEdgeColor_Supplement_theorem_D_3
-- name    : WeightedEdgeColor.Supplement.theorem_D_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:39:39.196479+00:00
-- url     : https://prove2.me/theorems/c3254a0b-be01-4b94-af1a-3fb8ad5c8445
-- title:
--   Theorem D.3 — bipartite multigraphs: $\chi'_w(G)\le(2+o(1))\Delta_w(G)$, in expected polynomial time, and two is best possible
-- statement:
--   For every $\varepsilon>0$ there is a constant $C_\varepsilon$ such that every finite bipartite weighted multigraph $G$ with edge weights in $(0,1]$ satisfies
--   $$
--   \chi'_w(G)\le(2+\varepsilon)\,\Delta_w(G)+C_\varepsilon ,
--   $$
--   that is, $\chi'_w(G)\le(2+o(1))\Delta_w(G)$; the constant is independent of the number of vertices, the edge multiplicities and the minimum positive weight. Moreover:
--   1. for each fixed $\varepsilon$ and rational input, such a coloring is constructed in expected polynomial running time;
--   2. the leading coefficient two is best possible: for every $c<2$ and every real $C$ some bipartite weighted multigraph has $\chi'_w(G)>c\,\Delta_w(G)+C$.
--
--   Here $\chi'_w(G)$ is the least number of colors in a proper weighted coloring (every color class has incident weight at most one at every vertex) and $\Delta_w(G)$ is the maximum weighted degree.
--
--   The result settles the factor two in terms of the maximum weighted degree asymptotically for bipartite multigraphs, the setting of multirate Clos network routing.
--
--   **Formalization Note** The algorithm is one randomized program of the logarithmic-cost RAM with fair coins (chosen after $\varepsilon$) that is Las Vegas on every bipartite input with rational weights: every halting run outputs a proper weighted coloring with at most $(2+\varepsilon)\Delta_w+C_\varepsilon$ colors, and the expected bit cost is at most $c(L+1)^d$.
--
--   Differences from the source:
--   - encoding: $\chi'_w(G)\le(2+o(1))\,X(G)$ (footnote 2, and the theorem's uniformity sentence) → for every $\varepsilon>0$ there is $C_\varepsilon$, chosen before the vertex and edge types and the graph, such that every bipartite multigraph with real weights in $(0,1]$ has a proper weighted coloring $E\to\{0,\dots,k-1\}$ with $k\le(2+\varepsilon)X(G)+C_\varepsilon$; reason: footnote 2 (p.2) defines the asymptotic bound this way; a proper coloring with $k$ colors is $\chi'_w(G)\le k$
--   - reading: "(expected) polynomial running time" on rational input, no machine named → one program of the logarithmic-cost RAM with fair coins (published TimeSpaceMA.RAM / SoftmaxAttnFD.Machine) and constants $c,d$, chosen after the accuracy and before the input, with expected bit cost at most $c(L+1)^d$ on the encoding of every input ($L$ its length), every halting run outputting a correct coloring (Las Vegas); reason: the paper names no machine and no encoding; bit cost on a RAM is the standard polynomial-time model, polynomial time is robust across reasonable machines, and the paper's constructions are Las Vegas (randomized with expected running time)
--   - encoding: rational weights and explicitly listed edges → RatGraph: vertex count $N$, edge list $(u_i,v_i,p_i,q_i)$ with $u_i\ne v_i<N$, $0<p_i\le q_i$, weight $p_i/q_i$; output color of edge $i$ in memory cell $i$; reason: one fixed encoding of the paper's input; any two reasonable encodings are polynomially related
--   - reading: the leading coefficient 2 is best possible → for every $c<2$ and every real $C$ there is a bipartite weighted multigraph $G$ with $\chi'_w(G)>c\,\Delta_w(G)+C$ (every proper weighted coloring into $k$ colors has $c\,\Delta_w(G)+C<k$); reason: for an asymptotic bound, optimality of the coefficient means no bound with a smaller coefficient and any additive constant holds; this is the stronger of the possible readings (not just $C=0$)
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Theorem D.3, p.60; Algorithm D.1, p.60; footnote 2, p.2; sharpness: the star of §5, p.13

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring
import Definitions.Def_TimeSpaceMA_RAM
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_WeightedEdgeColor_Supplement_maxWDeg
import Definitions.Def_WeightedEdgeColor_Supplement_IsBipartite
import Definitions.Def_WeightedEdgeColor_Supplement_RatGraph

set_option autoImplicit false

namespace WeightedEdgeColor

namespace Supplement

/-- Theorem D.3: every bipartite weighted multigraph satisfies `χ′_w(G) ≤ (2 + o(1))∆_w(G)`, with
the error uniform in graph order, multiplicity and minimum positive weight; for each fixed
accuracy and rational input the construction has expected polynomial running time; the leading
coefficient two is best possible.

Source: Gajjala, Khan, *Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing*,
preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Theorem D.3, p.60 (Algorithm D.1, p.60; sharpness: the star of §5, p.13); footnote 2, p.2.

**Formalization Note.** 1. `(2 + o(1))∆_w` is read by footnote 2: for every `ε > 0` there is
`C_ε`, chosen before the vertex and edge types and the graph, with `χ′_w(G) ≤ (2 + ε)∆_w(G) + C_ε`
for every bipartite multigraph with real weights in `(0, 1]`. 2. For the same `ε` and `C_ε`,
one program `P` of the log-cost RAM with fair coins and constants `c, d` that is Las Vegas
(`SoftmaxAttnFD.LasVegasWithin`) on every bipartite input with rational weights (`RatGraph`):
every halting run outputs a proper weighted coloring with at most `(2 + ε)∆_w + C_ε` colors and
the expected bit cost is at most `c·(L + 1)^d`. 3. "Best possible": for every `c < 2` and every
`C` some bipartite multigraph has `χ′_w(G) > c·∆_w(G) + C`. -/
theorem theorem_D_3 :
    (∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ,
      (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
        (G : WGraph V E), IsBipartite G →
        ∃ k : ℕ, (k : ℝ) ≤ (2 + ε) * maxWDeg G + Cε ∧ ∃ φ : E → Fin k, G.IsProperColoring φ) ∧
      ∃ (P : TimeSpaceMA.Program) (c d : ℕ), ∀ I : RatGraph, IsBipartite I.toWGraph →
        SoftmaxAttnFD.LasVegasWithin P I.mem
          (I.GoodOutput ((2 + ε) * maxWDeg I.toWGraph + Cε))
          ((c : ℝ) * ((I.bits : ℝ) + 1) ^ d)) ∧
    (∀ c : ℝ, c < 2 → ∀ C : ℝ, ∃ (V E : Type) (_ : Fintype V) (_ : DecidableEq V)
      (_ : Fintype E) (_ : DecidableEq E) (G : WGraph V E), IsBipartite G ∧
      ∀ (k : ℕ) (φ : E → Fin k), G.IsProperColoring φ → c * maxWDeg G + C < k) := by sorry

end Supplement

end WeightedEdgeColor
