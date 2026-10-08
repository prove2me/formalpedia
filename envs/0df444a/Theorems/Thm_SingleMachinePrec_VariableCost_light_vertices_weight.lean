-- Prove2me | Theorems.Thm_SingleMachinePrec_VariableCost_light_vertices_weight
-- name    : SingleMachinePrec.VariableCost.light_vertices_weight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:30:31.6765+00:00
-- url     : https://prove2.me/theorems/4292986a-1700-4352-b98a-981d542b548a
-- title:
--   §8, p. 664 — heavy nodes have weight 1, light nodes weight at most 1/k, total light weight at most n²/k
-- statement:
--   Let $G$ be a graph on $n$ vertices $v_1,\dots,v_n$, let $k \ge 1$, and let $S = S(G,k)$ be the scheduling instance of the proof of Theorem 8.1, with vertex cover graph $G^S_{\mathbf P}$ and node weights $w_{(a,b)} = p_a w_b$. Call the $n$ nodes $(v'_i, v''_i)$ *heavy* and all other nodes *light*. Then:
--
--   1. every heavy node has weight $1$;
--   2. every light node $u$ has weight $w_u \le 1/k$;
--   3. the total weight of the light nodes satisfies
--   $$
--   \sum_{u \text{ light}} w_u \le \frac{n^2}{k}.
--   $$
--
--   These bounds say that, up to an additive $n^2/k$, the weight of a vertex cover of $G^S_{\mathbf P}$ is the number of heavy nodes it contains.
--
--   **Formalization Note** The page also says that $G^S_{\mathbf P}$ "has at most $n^2$ vertices". That is false as printed: the pairs $(v'_i, v'_j)$ and $(v''_i, v''_j)$ with $i \neq j$ are incomparable nodes of weight $0$, so the graph can have up to $4n^2 - 2n$ nodes. Only the weight facts, which the argument uses, are formalized. The hypothesis $k \ge 1$ is implicit on the page (for $k < 1$ the light nodes would be heavier than $1$).
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 664, §8, proof of Theorem 8.1 (weights of G^S_P)

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_AdjacencyInstance
open scoped NNReal

namespace SingleMachinePrec.VariableCost

open Classical in
/-- §8, p. 664 (proof of Theorem 8.1). For the instance `S = adjacencyInstance G k` with
`k ≥ 1`: every node `(v′_i, v″_i)` of `G^S_P` has weight `1`; every other node has weight at
most `1/k`; and the total weight of the other ("light") nodes is at most `n²/k`. -/
theorem light_vertices_weight {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) (hk : 1 ≤ k) :
    (∀ i : Fin n, vertexWeight (adjacencyInstance G k) (heavy G k i) = 1) ∧
    (∀ u : IncPair (adjacencyInstance G k).P, (∀ i : Fin n, u ≠ heavy G k i) →
      vertexWeight (adjacencyInstance G k) u ≤ 1 / (k : ℝ)) ∧
    weight (adjacencyInstance G k)
        (Finset.univ.filter (fun u => ∀ i : Fin n, u ≠ heavy G k i)) ≤
      (n : ℝ) ^ 2 / (k : ℝ) := by sorry

end SingleMachinePrec.VariableCost
