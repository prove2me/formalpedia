-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_pair_resourceFeasible_iff_adj
-- name    : ResourceScheduling.Graph.pair_resourceFeasible_iff_adj
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:29:30.175775+00:00
-- url     : https://prove2.me/theorems/9c51eac3-ce1b-4625-9168-a035eb352623
-- title:
--   p. 15 — in the construction, two jobs can run simultaneously iff their vertices are adjacent
-- statement:
--   Let $G$ be a graph on the vertex set $V=\{1,\dots,N\}$ and consider the scheduling instance constructed from $G$ (one job $J_j$ per vertex, one unit resource $R_{\{j,k\}}$ per non-adjacent pair $\{j,k\}$, required by $J_j$ and $J_k$ only), on any machine environment. For two distinct vertices $j\ne k$,
--   $$\{J_j,J_k\}\ \text{is resource feasible}\quad\Longleftrightarrow\quad \{j,k\}\in E,$$
--   where a set $S$ of jobs is resource feasible when $\sum_{i\in S} r_{hi}\le s_h$ for every resource $R_h$.
--
--   In the paper's words: "two jobs can be executed simultaneously if and only if the corresponding vertices are adjacent". This is the property of the construction on which both reductions rest.
--
--   **Formalization Note.** Vertices are indexed from $0$. The machine count and speeds are arbitrary parameters, since the resource data of the construction do not depend on them.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 15, construction preceding Theorem 2 ("Thus, two jobs can be executed simultaneously if and only if the corresponding vertices are adjacent.")

import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Construction

namespace ResourceScheduling.Graph

/-- p. 15: in the constructed instance, two distinct jobs `J_j, J_k` can be executed
simultaneously (the set `{j, k}` satisfies every resource constraint) if and only if the vertices
`j, k` are adjacent. The machine environment plays no role. -/
theorem pair_resourceFeasible_iff_adj {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (y m : ℕ) (q : Fin m → ℝ) (hq : ∀ i, 0 < q i) (j k : Fin N) (hjk : j ≠ k) :
    ((construct G y).toInstance m q hq).ResourceFeasibleSet {j, k} ↔ G.Adj j k := by sorry

end ResourceScheduling.Graph
