-- Prove2me | Theorems.Thm_WeightedEdgeColor_Supplement_theorem_F_1
-- name    : WeightedEdgeColor.Supplement.theorem_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:42:10.124459+00:00
-- url     : https://prove2.me/theorems/10d8b022-e409-47da-be0d-e17db68b2173
-- title:
--   Theorem F.1 — loopless multigraphs: $\chi'_w(G)\le(\tfrac54h_\infty+o(1))\,\mathrm{bp}(G)$, by a randomized expected-polynomial-time algorithm
-- statement:
--   For every $\varepsilon>0$ there is a constant $C_\varepsilon$ such that every finite weighted multigraph without loops $G$ with edge weights in $(0,1]$ satisfies
--   $$
--   \chi'_w(G)\le\left(\tfrac54h_\infty+\varepsilon\right)\mathrm{bp}(G)+C_\varepsilon ,
--   $$
--   that is, $\chi'_w(G)\le(\tfrac54h_\infty+o(1))\,\mathrm{bp}(G)$. The constant is independent of the number of vertices, the edge multiplicities and the smallest edge weight.
--
--   Moreover, for rational weights and explicitly listed edges, each fixed accuracy $\varepsilon$ has a randomized algorithm with expected polynomial running time producing such a coloring.
--
--   Here $\chi'_w(G)$ is the least number of colors in a proper weighted coloring (every color class has incident weight at most one at every vertex) and $\mathrm{bp}(G)$ is the local bin-packing number, the largest over vertices $v$ of the least number of unit bins packing the weights of the edges at $v$.
--
--   Here $h_\infty=\sum_{j\ge1}1/r_j$ is the harmonic constant ($r_1=1$, $r_{j+1}=r_j(r_j+1)$), so $\tfrac54h_\infty=2.113787758446\ldots$; parallel edges are allowed and no bipartiteness is assumed.
--
--   **Formalization Note** For each $\varepsilon$ the algorithm is one randomized program of the logarithmic-cost RAM with fair coins that is Las Vegas on every input with rational weights and explicitly listed edges: every halting run outputs a proper weighted coloring with at most $(\tfrac54h_\infty+\varepsilon)\mathrm{bp}+C_\varepsilon$ colors (the same $C_\varepsilon$), and the expected bit cost is at most $c(L+1)^d$, $L$ the input length.
--
--   Differences from the source:
--   - encoding: $\chi'_w(G)\le(\tfrac54h_\infty+o(1))\,X(G)$ (footnote 2, and the theorem's uniformity sentence) → for every $\varepsilon>0$ there is $C_\varepsilon$, chosen before the vertex and edge types and the graph, such that every loopless multigraph with real weights in $(0,1]$ has a proper weighted coloring $E\to\{0,\dots,k-1\}$ with $k\le(\tfrac54h_\infty+\varepsilon)X(G)+C_\varepsilon$; reason: footnote 2 (p.2) defines the asymptotic bound this way; a proper coloring with $k$ colors is $\chi'_w(G)\le k$
--   - encoding: $\tfrac54h_\infty=2.113787758446\ldots$ → $\tfrac54\cdot h_\infty$ with $h_\infty$ the sum of the series; reason: the decimal is only an evaluation of the same constant
--   - reading: "(expected) polynomial running time" on rational input, no machine named → one program of the logarithmic-cost RAM with fair coins (published TimeSpaceMA.RAM / SoftmaxAttnFD.Machine) and constants $c,d$, chosen after the accuracy and before the input, with expected bit cost at most $c(L+1)^d$ on the encoding of every input ($L$ its length), every halting run outputting a correct coloring (Las Vegas); reason: the paper names no machine and no encoding; bit cost on a RAM is the standard polynomial-time model, polynomial time is robust across reasonable machines, and the paper's constructions are Las Vegas (randomized with expected running time)
--   - encoding: rational weights and explicitly listed edges → RatGraph: vertex count $N$, edge list $(u_i,v_i,p_i,q_i)$ with $u_i\ne v_i<N$, $0<p_i\le q_i$, weight $p_i/q_i$; output color of edge $i$ in memory cell $i$; reason: one fixed encoding of the paper's input; any two reasonable encodings are polynomially related
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Theorem F.1, p.71; $h_\infty$ defined on p.64

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring
import Definitions.Def_WeightedEdgeColor_WGraph_bp
import Definitions.Def_TimeSpaceMA_RAM
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_WeightedEdgeColor_Supplement_hInf
import Definitions.Def_WeightedEdgeColor_Supplement_RatGraph

set_option autoImplicit false

namespace WeightedEdgeColor

namespace Supplement

/-- Theorem F.1: every weighted multigraph without loops satisfies
`χ′_w(G) ≤ ((5/4)h∞ + o(1)) bp(G)`; more precisely for each `ε > 0` there is `C_ε` such that at most
`((5/4)h∞ + ε) bp(G) + C_ε` colors suffice, the constant independent of the number of vertices,
parallel multiplicities and the smallest edge weight; for rational weights and explicitly listed
edges each fixed accuracy has a randomized algorithm with expected polynomial running time.

Source: Gajjala, Khan, *Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing*,
preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Theorem F.1, p.71; h∞ defined on p.64.

**Formalization Note.** 1. `(c₀ + o(1)) bp` is read by footnote 2 (p.2) and the theorem's own uniformity clause: for every
`ε > 0` there is `Cε`, chosen before the vertex and edge types and the graph, with `χ′_w(G) ≤ (c₀
+ ε) bp(G) + Cε` for every loopless multigraph (every `WGraph`) with real weights in `(0, 1]`;
`χ′_w(G) ≤ X` is "a proper weighted coloring `E → Fin k` with `k ≤ X`". `(5/4)h∞` is `5 / 4 *
hInf`, not its decimal expansion `2.113787758446…`.
2. For the same `ε` and `Cε`, one program `P` of the logarithmic-cost RAM with fair coins and
constants `c, d` that is Las Vegas (`SoftmaxAttnFD.LasVegasWithin`) on every input with rational
weights and explicitly listed edges (`RatGraph`): every halting run outputs a proper weighted
coloring with at most `(c₀ + ε) bp + Cε` colors, and the expected bit cost is at most `c·(L +
1)^d`, `L` the input length. The paper names no machine.
-/
theorem theorem_F_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ,
      (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
        (G : WGraph V E),
        ∃ k : ℕ, (k : ℝ) ≤ (5 / 4 * hInf + ε) * (G.bp : ℝ) + Cε ∧ ∃ φ : E → Fin k, G.IsProperColoring φ) ∧
      ∃ (P : TimeSpaceMA.Program) (c d : ℕ), ∀ I : RatGraph,
        SoftmaxAttnFD.LasVegasWithin P I.mem
          (I.GoodOutput ((5 / 4 * hInf + ε) * (I.toWGraph.bp : ℝ) + Cε))
          ((c : ℝ) * ((I.bits : ℝ) + 1) ^ d) := by sorry

end Supplement

end WeightedEdgeColor
