-- Prove2me | Theorems.Thm_WeightedEdgeColor_Supplement_theorem_B_2
-- name    : WeightedEdgeColor.Supplement.theorem_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:38:51.354132+00:00
-- url     : https://prove2.me/theorems/cdfb1684-f9fe-489c-99a7-6679bbc6f9f8
-- title:
--   Theorem B.2 — weighted Shannon: $\chi'_w(G)\le3\lceil\Delta_w(G)\rceil$ for loopless multigraphs, deterministically in polynomial time, and three is best possible
-- statement:
--   Let $G$ be a finite weighted multigraph without loops, with edge weights in $(0,1]$. Then
--   $$
--   \chi'_w(G)\le3\lceil\Delta_w(G)\rceil .
--   $$
--   Moreover:
--   1. such a coloring can be found by a deterministic polynomial-time algorithm;
--   2. the leading coefficient three is best possible: for every $c<3$ and every real $C$ some loopless weighted multigraph has $\chi'_w(G)>c\lceil\Delta_w(G)\rceil+C$.
--
--   Here $\chi'_w(G)$ is the least number of colors in a proper weighted coloring (every color class has incident weight at most one at every vertex) and $\Delta_w(G)$ is the maximum weighted degree. The bound has no additive constant.
--
--   This is an exact weighted analogue of Shannon's theorem $\chi'(G)\le\lfloor3\Delta(G)/2\rfloor$ in terms of the total weight at a vertex.
--
--   **Formalization Note** The algorithm clause is stated for inputs with rational weights and explicitly listed edges, encoded in the memory of a logarithmic-cost RAM; the algorithm is one coin-free program whose bit cost on every input is at most $c(L+1)^d$, $L$ the input length, and whose output is a proper weighted coloring with at most $3\lceil\Delta_w\rceil$ colors.
--
--   Differences from the source:
--   - encoding: $\chi'_w(G)\le3\lceil\Delta_w(G)\rceil$ → a proper weighted coloring $E\to\{0,\dots,k-1\}$ with $k\le3\lceil\Delta_w(G)\rceil$, for every finite loopless multigraph with real weights in $(0,1]$; reason: a proper coloring with $k$ colors is $\chi'_w(G)\le k$
--   - reading: "Such a coloring can be found by a deterministic polynomial-time algorithm" (no input class, no machine named) → one coin-free program of the logarithmic-cost RAM (published TimeSpaceMA.RAM, SoftmaxAttnFD.DeterministicWithin) and constants $c,d$ such that on every input with rational weights and explicitly listed edges it halts within bit cost $c(L+1)^d$ with a proper weighted coloring using at most $3\lceil\Delta_w\rceil$ colors; reason: a bit-cost algorithm reads only finitely described weights and the paper analyses running time only for rational input; the existence bound itself is kept for all real weights; bit cost on a RAM is the standard polynomial-time model
--   - encoding: rational weights and explicitly listed edges → RatGraph: vertex count $N$, edge list $(u_i,v_i,p_i,q_i)$ with $u_i\ne v_i<N$, $0<p_i\le q_i$, weight $p_i/q_i$; output color of edge $i$ in memory cell $i$; reason: one fixed encoding of the paper's input; any two reasonable encodings are polynomially related
--   - reading: the leading coefficient 3 is best possible → for every $c<3$ and every real $C$ there is a loopless weighted multigraph $G$ with $\chi'_w(G)>c\,\lceil\Delta_w(G)\rceil+C$ (every proper weighted coloring into $k$ colors has $c\,\lceil\Delta_w(G)\rceil+C<k$); reason: for an asymptotic bound, optimality of the coefficient means no bound with a smaller coefficient and any additive constant holds; this is the stronger of the possible readings (not just $C=0$)
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Theorem B.2, p.31; Algorithm B.1, p.32; sharpness §B.4, p.32

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring
import Definitions.Def_TimeSpaceMA_RAM
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_WeightedEdgeColor_Supplement_maxWDeg
import Definitions.Def_WeightedEdgeColor_Supplement_RatGraph

set_option autoImplicit false

namespace WeightedEdgeColor

namespace Supplement

/-- Theorem B.2: every weighted multigraph without loops satisfies `χ′_w(G) ≤ 3⌈∆_w(G)⌉`; such
a coloring can be found by a deterministic polynomial-time algorithm; the leading coefficient
three is best possible.

Source: Gajjala, Khan, *Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing*,
preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Theorem B.2, p.31 (Algorithm B.1, p.32; sharpness §B.4, p.32).

**Formalization Note.** 1. The bound holds for every finite loopless multigraph with real weights
in `(0, 1]`, with no additive constant. 2. The algorithm clause: one coin-free program `P` of the
logarithmic-cost RAM (`TimeSpaceMA`) and constants `c, d` such that on the encoding of every
input with rational weights and explicitly listed edges (`RatGraph`) it halts within bit cost
`c·(L + 1)^d` (`L` the input length) with a proper weighted coloring using at most `3⌈∆_w⌉`
colors. The paper names no machine. 3. "Best possible": for every `c < 3` and every `C` some
loopless multigraph has `χ′_w(G) > c⌈∆_w(G)⌉ + C`. -/
theorem theorem_B_2 :
    (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : WGraph V E),
      ∃ k : ℕ, (k : ℝ) ≤ 3 * ((⌈maxWDeg G⌉ : ℤ) : ℝ) ∧ ∃ φ : E → Fin k, G.IsProperColoring φ) ∧
    (∃ (P : TimeSpaceMA.Program) (c d : ℕ), ∀ I : RatGraph,
      SoftmaxAttnFD.DeterministicWithin P I.mem
        (I.GoodOutput (3 * ((⌈maxWDeg I.toWGraph⌉ : ℤ) : ℝ)))
        ((c : ℝ) * ((I.bits : ℝ) + 1) ^ d)) ∧
    (∀ c : ℝ, c < 3 → ∀ C : ℝ, ∃ (V E : Type) (_ : Fintype V) (_ : DecidableEq V)
      (_ : Fintype E) (_ : DecidableEq E) (G : WGraph V E),
      ∀ (k : ℕ) (φ : E → Fin k), G.IsProperColoring φ →
        c * ((⌈maxWDeg G⌉ : ℤ) : ℝ) + C < k) := by sorry

end Supplement

end WeightedEdgeColor
