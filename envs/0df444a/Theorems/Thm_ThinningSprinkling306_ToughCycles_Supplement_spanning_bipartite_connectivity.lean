-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_Supplement_spanning_bipartite_connectivity
-- name    : ThinningSprinkling306.ToughCycles.Supplement.spanning_bipartite_connectivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:45:32.931212+00:00
-- url     : https://prove2.me/theorems/3cd62453-5b43-45e7-a8f0-072414f09038
-- title:
--   Theorem 1.5 — spanning bipartite subgraphs of proportional connectivity
-- statement:
--   All graphs below are finite simple undirected graphs. A family $G_j$ has $n_j$ vertices with $n_j\to\infty$; the index may follow any subsequence of vertex counts. All conclusions are eventual. Sampling retains each vertex independently with probability $p_j\in[0,1]$.
--
--   There is an absolute constant $a>0$ such that for every family of $k_j$-vertex-connected graphs with $k_j/\log n_j\to\infty$, eventually there is a spanning edge subgraph $H_j\le G_j$ with a bipartition and
--   $$
--   \kappa(H_j)\ge a k_j.
--   $$
--   The graph $H_j$ has the entire original vertex set. Its bipartition is a witness, and its connectivity is vertex connectivity with the standard cardinality clause. This retains a linear proportion of connectivity rather than a logarithmically smaller one.
--
--   Differences from the source:
--   - encoding: asymptotics relative to n tending to infinity → arbitrary Fin n_j graph families with real Tendsto limits and eventual conclusions; reason: makes all omega, little-o and eventual quantifiers explicit without fixing a rate or subsequence
--   - encoding: real-valued connectivity lower bound → published integer vertex connectivity compared in the reals with the cardinality clause; reason: exactly the ceiling-threshold convention, including complete graphs and tiny samples
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 3, Theorem 1.5 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_GraphParameters

open Filter

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- Theorem 1.5: the witness is an edge subgraph on the full original vertex type. -/
theorem spanning_bipartite_connectivity :
    ∃ a : ℝ, 0 < a ∧
    ∀ (n k : ℕ → ℕ) (G : (j : ℕ) → SimpleGraph (Fin (n j))),
      Tendsto (fun j => (n j : ℝ)) atTop atTop →
      (∀ j, ConnectedAt (G j) Finset.univ (k j : ℝ)) →
      Tendsto (fun j => (k j : ℝ) / Real.log (n j)) atTop atTop →
      ∀ᶠ j in atTop, ∃ H : SimpleGraph (Fin (n j)), H ≤ G j ∧
        (∃ color : Fin (n j) → Bool, ∀ u v, H.Adj u v → color u ≠ color v) ∧
        ConnectedAt H Finset.univ (a * (k j : ℝ)) := by sorry

end ThinningSprinkling306.ToughCycles.Supplement
