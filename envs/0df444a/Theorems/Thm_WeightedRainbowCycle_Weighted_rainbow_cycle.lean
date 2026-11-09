-- Prove2me | Theorems.Thm_WeightedRainbowCycle_Weighted_rainbow_cycle
-- name    : WeightedRainbowCycle.Weighted.rainbow_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:18.852144+00:00
-- url     : https://prove2.me/theorems/3eef993a-c27c-4105-bcda-56f4e9f8d296
-- title:
--   Theorem 1.1 (corrected: positive ∆ and ℓ)
-- statement:
--   There exists a single integer $N_0\ge3$, independent of all graph, color, list, weight, and parameter data, such that the following holds. Let $G$ be a loopless weighted list graph on $N\ge N_0$ vertices, let $\ell\ge1$ be any integer and $\Delta>0$ any real number. Every edge has a nonnegative real weight and a nonempty finite list $L(e)$ from an arbitrary ambient color set, with $|L(e)|\le\ell$. Suppose $\deg_c(u)\le\Delta$ for every vertex and color. If
--
--   $$d(G)\ge13\Delta\ell2^\ell\log N\log\log N,$$
--
--   then $G$ contains a genuine cycle whose full edge lists are pairwise disjoint. Here $d(G)=2\sum_e w(e)/N$, and every logarithm is natural. Equality at the threshold is included. In the multigraph representation two distinct parallel edges may form a cycle; on simple graphs every such cycle has length at least three.
--
--   This is the complete weighted list-color headline theorem, retaining its exact coefficient and arbitrary nonnegative real weights. It does not assume maximal logarithmic density, expansion, a differential inequality, proper coloring, or connectivity.
--
--   Differences from the source:
--   - correction: Delta may be zero or negative → Delta > 0; reason: for every arbitrarily large N the edgeless graph, C = {red}, ell = 1, Delta = 0 satisfies every printed assumption and 0 ≥ 0 but has no cycle; the edgeless graph with C empty and Delta < 0 fails the same way
--   - correction: ell may be zero → ell ≥ 1; reason: for every arbitrarily large N the edgeless graph, C = {red}, ell = 0, Delta = 1 satisfies every printed assumption and 0 ≥ 0 but has no cycle
--   - reading: the color-degree sum prints e incident to S, while the prose names u → incidence to u; reason: uses the adjacent explicit definition of the color-degree at vertex u
--   - generalization: graphs in the usual simple-graph reading → loopless finite multigraphs with distinct edge identities and length-two cycles allowed; reason: every simple graph embeds unchanged; weighted edge-counting arguments also retain parallel edges
--   - encoding: finite vertices and edges, with an arbitrary color set → finite vertex and edge types, finite edge lists, and an arbitrary ambient color type; reason: these represent every finite input graph and every finite list without restricting colors or real weights
--   - reading: for sufficiently large N → one existential N0 ≥ 3 before every graph, color, weight, ell and Delta quantifier; reason: the source does not say whether the threshold may depend on ell and Delta, and this is the stronger reading; p. 9 bounds the graph-independent error using f(1/2) ≥ log(4/3) and log n ≤ log N, without requiring n to grow
-- source:
--   Andrew D. Lin, STOC 2027 submission #545 (October 2026), Theorem 1.1, p. 2, restated p. 8; proof, pp. 8–9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/545.pdf

import Definitions.Def_WeightedRainbowCycle_Weighted_Reachability

set_option autoImplicit false

namespace WeightedRainbowCycle.Weighted

/-- Theorem 1.1, pp. 2, 8 (corrected: delta > 0, ell >= 1).
At delta = 0 or ell = 0 arbitrarily large edgeless graphs contradict the printed statement. -/
theorem rainbow_cycle :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ (V E C : Type*) [Fintype V] [Fintype E]
        [DecidableEq V] [DecidableEq E] [DecidableEq C]
        (G : Model V E C) (ell : ℕ) (delta : ℝ),
        N₀ ≤ Fintype.card V → 1 ≤ ell → 0 < delta → G.Admissible ell delta →
        13 * delta * (ell : ℝ) * (2 : ℝ) ^ ell * Real.log (Fintype.card V) *
          Real.log (Real.log (Fintype.card V)) ≤ G.degree →
        HasRainbowCycle G := by sorry

end WeightedRainbowCycle.Weighted
