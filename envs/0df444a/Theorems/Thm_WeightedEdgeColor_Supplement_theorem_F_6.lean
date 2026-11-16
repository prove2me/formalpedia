-- Prove2me | Theorems.Thm_WeightedEdgeColor_Supplement_theorem_F_6
-- name    : WeightedEdgeColor.Supplement.theorem_F_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:42:35.090072+00:00
-- url     : https://prove2.me/theorems/8d6aaf45-c505-42f3-b697-29e02b681104
-- title:
--   Theorem F.6 — loopless multigraphs: $\chi'_w(G)\le(1.999+o(1))\,\mathrm{bp}(G)$, by a randomized expected-polynomial-time algorithm
-- statement:
--   For every $\varepsilon>0$ there is a constant $C_\varepsilon$ such that every finite weighted loopless multigraph $G$ with edge weights in $(0,1]$ satisfies
--   $$
--   \chi'_w(G)\le\left(1.999+\varepsilon\right)\mathrm{bp}(G)+C_\varepsilon ,
--   $$
--   that is, $\chi'_w(G)\le(1.999+o(1))\,\mathrm{bp}(G)$. The constant is independent of the number of vertices, the edge multiplicities and the smallest edge weight.
--
--   Moreover, for rational weights and explicitly listed edges, such a coloring can be found by a randomized algorithm with expected polynomial running time for every fixed $\varepsilon>0$.
--
--   Here $\chi'_w(G)$ is the least number of colors in a proper weighted coloring (every color class has incident weight at most one at every vertex) and $\mathrm{bp}(G)$ is the local bin-packing number, the largest over vertices $v$ of the least number of unit bins packing the weights of the edges at $v$.
--
--   The coefficient is below two for arbitrary loopless multigraphs, where the triangle with parallel edges shows that no coefficient below $3/2$ is possible.
--
--   **Formalization Note** For each $\varepsilon$ the algorithm is one randomized program of the logarithmic-cost RAM with fair coins that is Las Vegas on every input with rational weights and explicitly listed edges: every halting run outputs a proper weighted coloring with at most $(1.999+\varepsilon)\mathrm{bp}+C_\varepsilon$ colors (the same $C_\varepsilon$), and the expected bit cost is at most $c(L+1)^d$, $L$ the input length.
--
--   Differences from the source:
--   - encoding: $\chi'_w(G)\le(1.999+o(1))\,X(G)$ (footnote 2, and the theorem's uniformity sentence) → for every $\varepsilon>0$ there is $C_\varepsilon$, chosen before the vertex and edge types and the graph, such that every loopless multigraph with real weights in $(0,1]$ has a proper weighted coloring $E\to\{0,\dots,k-1\}$ with $k\le(1.999+\varepsilon)X(G)+C_\varepsilon$; reason: footnote 2 (p.2) defines the asymptotic bound this way; a proper coloring with $k$ colors is $\chi'_w(G)\le k$
--   - encoding: the coefficient $1.999$ → $1999/1000$; reason: exact equality; the paper's $\kappa=1999/1000$ (p.77)
--   - reading: "(expected) polynomial running time" on rational input, no machine named → one program of the logarithmic-cost RAM with fair coins (published TimeSpaceMA.RAM / SoftmaxAttnFD.Machine) and constants $c,d$, chosen after the accuracy and before the input, with expected bit cost at most $c(L+1)^d$ on the encoding of every input ($L$ its length), every halting run outputting a correct coloring (Las Vegas); reason: the paper names no machine and no encoding; bit cost on a RAM is the standard polynomial-time model, polynomial time is robust across reasonable machines, and the paper's constructions are Las Vegas (randomized with expected running time)
--   - encoding: rational weights and explicitly listed edges → RatGraph: vertex count $N$, edge list $(u_i,v_i,p_i,q_i)$ with $u_i\ne v_i<N$, $0<p_i\le q_i$, weight $p_i/q_i$; output color of edge $i$ in memory cell $i$; reason: one fixed encoding of the paper's input; any two reasonable encodings are polynomially related
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Theorem F.6, pp.76–77 ($\kappa=1999/1000$, p.77)

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring
import Definitions.Def_WeightedEdgeColor_WGraph_bp
import Definitions.Def_TimeSpaceMA_RAM
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_WeightedEdgeColor_Supplement_RatGraph

set_option autoImplicit false

namespace WeightedEdgeColor

namespace Supplement

/-- Theorem F.6: every weighted loopless multigraph satisfies `χ′_w(G) ≤ (1.999 + o(1)) bp(G)`;
equivalently for every `ε > 0` there is `C_ε`, independent of graph order, multiplicity and minimum
positive weight, with `χ′_w(G) ≤ (1.999 + ε) bp(G) + C_ε`; for rational weights and explicitly
listed edges such a coloring can be found by a randomized algorithm with expected polynomial
running time for every fixed `ε > 0`.

Source: Gajjala, Khan, *Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing*,
preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Theorem F.6, pp.76–77 (κ = 1999/1000, p.77).

**Formalization Note.** 1. `(c₀ + o(1)) bp` is read by footnote 2 (p.2) and the theorem's own uniformity clause: for every
`ε > 0` there is `Cε`, chosen before the vertex and edge types and the graph, with `χ′_w(G) ≤ (c₀
+ ε) bp(G) + Cε` for every loopless multigraph (every `WGraph`) with real weights in `(0, 1]`;
`χ′_w(G) ≤ X` is "a proper weighted coloring `E → Fin k` with `k ≤ X`". `1.999` is written `1999 /
1000` (the paper's `κ`, p.77).
2. For the same `ε` and `Cε`, one program `P` of the logarithmic-cost RAM with fair coins and
constants `c, d` that is Las Vegas (`SoftmaxAttnFD.LasVegasWithin`) on every input with rational
weights and explicitly listed edges (`RatGraph`): every halting run outputs a proper weighted
coloring with at most `(c₀ + ε) bp + Cε` colors, and the expected bit cost is at most `c·(L +
1)^d`, `L` the input length. The paper names no machine.
-/
theorem theorem_F_6 (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ,
      (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
        (G : WGraph V E),
        ∃ k : ℕ, (k : ℝ) ≤ (1999 / 1000 + ε) * (G.bp : ℝ) + Cε ∧ ∃ φ : E → Fin k, G.IsProperColoring φ) ∧
      ∃ (P : TimeSpaceMA.Program) (c d : ℕ), ∀ I : RatGraph,
        SoftmaxAttnFD.LasVegasWithin P I.mem
          (I.GoodOutput ((1999 / 1000 + ε) * (I.toWGraph.bp : ℝ) + Cε))
          ((c : ℝ) * ((I.bits : ℝ) + 1) ^ d) := by sorry

end Supplement

end WeightedEdgeColor
