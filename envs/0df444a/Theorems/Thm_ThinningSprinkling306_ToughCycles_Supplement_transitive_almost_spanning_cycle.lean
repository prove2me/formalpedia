-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_Supplement_transitive_almost_spanning_cycle
-- name    : ThinningSprinkling306.ToughCycles.Supplement.transitive_almost_spanning_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:46:01.633215+00:00
-- url     : https://prove2.me/theorems/001bba27-5813-435c-ab6d-3a75eb6ce42d
-- title:
--   Theorem 1.7 — almost spanning cycles in vertex-transitive graphs
-- statement:
--   All graphs below are finite simple undirected graphs. A family $G_j$ has $n_j$ vertices with $n_j\to\infty$; the index may follow any subsequence of vertex counts. All conclusions are eventual. Sampling retains each vertex independently with probability $p_j\in[0,1]$.
--
--   For every family of connected $d_j$-regular vertex-transitive graphs with
--   $$
--   \frac{d_j}{(\log n_j)^3\log\log n_j}\longrightarrow\infty,
--   $$
--   and every fixed $\delta>0$, eventually $G_j$ contains a simple cycle of length at least
--   $$
--   (1-\delta)n_j.
--   $$
--   Vertex transitivity includes all graph automorphisms and is not restricted to Cayley graphs. The full printed degree threshold and every loss are retained. The paper derives this companion theorem from Theorems 1.3 and 10.1.
--
--   Differences from the source:
--   - encoding: asymptotics relative to n tending to infinity → arbitrary Fin n_j graph families with real Tendsto limits and eventual conclusions; reason: makes all omega, little-o and eventual quantifiers explicit without fixing a rate or subsequence
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 4, Theorem 1.7 (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_GraphParameters
import Definitions.Def_DerandSq_IsVertexTransitive
import Definitions.Def_ThinningSprinkling306_ToughCycles_Paths

open Filter

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- Theorem 1.7: every positive loss, with the printed log log factor retained. -/
theorem transitive_almost_spanning_cycle
    (n d : ℕ → ℕ) (G : (j : ℕ) → SimpleGraph (Fin (n j)))
    (hn : Tendsto (fun j => (n j : ℝ)) atTop atTop)
    (hgraphs : ∀ j, (G j).Connected ∧ RegularOn (G j) Finset.univ (d j) ∧
      DerandSq.IsVertexTransitive (G j))
    (hdegree : Tendsto
      (fun j => (d j : ℝ) / (Real.log (n j) ^ 3 * Real.log (Real.log (n j))))
      atTop atTop) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, LongCycle (G j) ((1 - δ) * (n j : ℝ)) := by sorry

end ThinningSprinkling306.ToughCycles.Supplement
