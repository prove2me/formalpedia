-- Prove2me | Theorems.Thm_WeightedRainbowCycle_Weighted_Supplement_proper_rainbow_cycle
-- name    : WeightedRainbowCycle.Weighted.Supplement.proper_rainbow_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:37:19.608487+00:00
-- url     : https://prove2.me/theorems/7b9aa57f-4d2e-4bd2-8e60-f4b1ac0e88f0
-- title:
--   Theorem 2.1 (corrected: sufficiently large N)
-- statement:
--   There exists a single integer $N_0\ge3$, independent of every graph and coloring, such that the following holds. Let $G$ be a finite loopless graph on $N\ge N_0$ vertices whose edges are properly colored from an arbitrary color set $C$: each edge receives exactly one color, and no two edges sharing an endpoint receive the same color. Write $d(G)=2|E(G)|/N$ for its average degree, and let $\log$ denote the natural logarithm. If
--
--   $$d(G)\ge 9\log N\,\log\log N,$$
--
--   then $G$ contains a rainbow cycle, that is, a cycle on which no color appears more than once. Equality at the threshold is included.
--
--   This is the unweighted, single-color case of the rainbow cycle theorem, with the explicit constant $9$. It is a companion of the mission's weighted list-colored goal: specializing that goal to unit weights, $\ell=1$ and $\Delta=1$ only gives the constant $13\cdot2=26$, so this sharper constant is a separate result.
--
--   **Formalization Note** The graph is the published weighted list-graph model with every edge weight equal to $1$ and the admissibility condition with list size at most $1$ and color-degree at most $1$. Since lists are nonempty, each edge then has exactly one color, and color-degree at most one at every vertex is exactly properness. The model's average degree is then $2|E|/N$. A rainbow cycle is a closed walk of length at least two with distinct edges and distinct vertices whose edge colors are pairwise distinct.
--
--   Differences from the source:
--   - correction: every N-vertex graph, with no size threshold → one existential N0 ≥ 3 quantified before all graph and color data, and N ≥ N0; reason: the path a–b–c with ab red and bc blue is properly edge-colored, has d = 4/3 ≥ 9·ln 3·ln ln 3 ≈ 0.93, and has no cycle; the proof on p. 6 only gives d(H) ≤ (8 + o(1)) log n log log n < 9 log n log log n, a large-N bound, and Theorem 1.1 itself is stated for sufficiently large N
--   - generalization: graphs in the usual simple-graph reading → loopless finite multigraphs with distinct edge identities; reason: every simple graph embeds unchanged, and in a proper coloring two parallel edges carry distinct colors and already form a rainbow cycle of length two
--   - encoding: a properly edge-colored graph with an arbitrary color set → the published model with unit weights and Admissible 1 1 over an arbitrary ambient color type; reason: with nonempty lists, list size at most one and color-degree at most one at each vertex is exactly a proper edge coloring
-- source:
--   Andrew D. Lin, STOC 2027 submission #545 (October 2026), Theorem 2.1, p. 5; proof, pp. 5–6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/545.pdf

import Definitions.Def_WeightedRainbowCycle_Weighted_Reachability

set_option autoImplicit false

namespace WeightedRainbowCycle.Weighted.Supplement

/-- Theorem 2.1, p. 5 (corrected: sufficiently large N, one uniform threshold).
A properly edge-colored graph is a model with unit weights and `Admissible 1 1`:
one color per edge, at most one edge of each color at every vertex.
The printed statement fails at N = 3 (a two-colored path). -/
theorem proper_rainbow_cycle :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ (V E C : Type*) [Fintype V] [Fintype E]
        [DecidableEq V] [DecidableEq E] [DecidableEq C]
        (G : Model V E C),
        N₀ ≤ Fintype.card V → (∀ e, G.weight e = 1) → G.Admissible 1 1 →
        9 * Real.log (Fintype.card V) * Real.log (Real.log (Fintype.card V)) ≤ G.degree →
        HasRainbowCycle G := by sorry

end WeightedRainbowCycle.Weighted.Supplement
