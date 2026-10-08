-- Prove2me | Theorems.Thm_SingleMachinePrec_VariableCost_heavy_subgraph_iso
-- name    : SingleMachinePrec.VariableCost.heavy_subgraph_iso
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:30:39.743793+00:00
-- url     : https://prove2.me/theorems/a5c82f44-2ddd-43b3-8b2a-5c6b660dca01
-- title:
--   §8, p. 664 — the subgraph of $G^S_{\mathbf P}$ induced by the weight-1 nodes is isomorphic to $G$
-- statement:
--   Let $G$ be a graph on vertices $v_1,\dots,v_n$, let $k > 0$, and let $S = S(G,k)$ be the scheduling instance of the proof of Theorem 8.1. Then:
--
--   1. for all $i, j$, the nodes $(v'_i, v''_i)$ and $(v'_j, v''_j)$ are adjacent in $G^S_{\mathbf P}$ if and only if $\{v_i, v_j\} \in E$;
--   2. if $k > 1$, the subgraph of $G^S_{\mathbf P}$ induced by the nodes of weight $1$ is isomorphic to $G$, by an isomorphism sending $(v'_i, v''_i)$ to $v_i$:
--   $$
--   G^S_{\mathbf P}\bigl[\{u : w_u = 1\}\bigr] \cong G .
--   $$
--
--   Together with the weight bounds, this identifies vertex covers of $G^S_{\mathbf P}$, up to light nodes, with vertex covers of $G$.
--
--   **Formalization Note** For $k = 1$ some light nodes $(v'_i, v''_j)$, $j < i$, have weight $k^{j-i} = 1$ as well, so the set of weight-1 nodes is larger than the set of heavy nodes; the isomorphism is therefore stated under $k > 1$, while the adjacency equivalence (1) holds for every $k$.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 664, §8, proof of Theorem 8.1 (isomorphism with G)

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_AdjacencyInstance
open scoped NNReal

namespace SingleMachinePrec.VariableCost

/-- §8, p. 664 (proof of Theorem 8.1). For the instance `S = adjacencyInstance G k`:
(1) two nodes `(v′_i, v″_i)` and `(v′_j, v″_j)` are adjacent in `G^S_P` if and only if
`{v_i, v_j} ∈ E`; (2) if `k > 1`, the subgraph of `G^S_P` induced by the nodes of weight `1`
is isomorphic to `G`, by an isomorphism sending `(v′_i, v″_i)` to `v_i`. -/
theorem heavy_subgraph_iso {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) :
    (∀ i j : Fin n,
      (vertexCoverGraph (adjacencyInstance G k).P).Adj (heavy G k i) (heavy G k j) ↔
        G.Adj i j) ∧
    (1 < k →
      ∃ f : (vertexCoverGraph (adjacencyInstance G k).P).induce
          {u | vertexWeight (adjacencyInstance G k) u = 1} ≃g G,
        ∀ (i : Fin n) (h : heavy G k i ∈ {u | vertexWeight (adjacencyInstance G k) u = 1}),
          f ⟨heavy G k i, h⟩ = i) := by sorry

end SingleMachinePrec.VariableCost
