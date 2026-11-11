-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_triangle_finding_lower_bound
-- name    : QuantumTriangleFinding.Search.triangle_finding_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:49.614128+00:00
-- url     : https://prove2.me/theorems/b0ae5da1-0134-4cb1-8333-39ae7c934955
-- title:
--   Theorem 1.1 — Quantum query lower bound for triangle finding
-- statement:
--   There are absolute constants $c>0$ and $N_0\in\mathbb N$ such that for every $N\ge N_0$, every $t$-query quantum algorithm on an arbitrary finite complex workspace and every input-independent final decoder, the following implication holds. If the algorithm outputs a valid triangle with probability at least $2/3$ on every simple undirected $N$-vertex graph containing a triangle, then
--   $$t\ge cN^{13/12}.$$
--   All adjacency-matrix queries are allowed, including repeated vertices and both edge orientations. The oracle contains exactly the graph's adjacency bits. No condition is imposed on the output on triangle-free graphs. The constants precede every size, query horizon, workspace, circuit and decoder, so this is the full uniform $\Omega(N^{13/12})$ search lower bound for every sufficiently large $N$.
--
--   The statement assumes no tripartite promise, sparsity, unique triangle or known restricted host. It addresses operational query circuits, rather than replacing the conclusion by an estimate for a comparison operator.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected hosts and three-edge triangles → SimpleGraph (Fin N), sorted endpoint pairs and unordered three-vertex cliques; circuits may query every ordered vertex pair; reason: finite relabeling and the vertex-set/edge-set correspondence preserve every instance; loops and host nonedges return zero and both edge orientations agree
--   - encoding: the asymptotic lower bound Ω(N^(13/12)) in the bounded-error search model → front-quantified c > 0 and N₀ followed by all N ≥ N₀ and all operational circuits with pointwise success at least 2/3; reason: this is the uniform eventual meaning of Ω; the exponent is real 13/12 and arbitrary final measurements are represented by input-independent coherent dilation and basis decoding
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Theorem 1.1, p. 3; proof and arbitrary-N padding, p. 34

import Definitions.Def_QuantumTriangleFinding_Search_GraphModel

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Theorem 1.1, p.3 (proof p.34): all graphs, all finite workspaces and every sufficiently large N.
The complete host represents every simple undirected graph by its independent unordered edge bits;
the circuit may query the full adjacency matrix, including loops and both orientations. -/
theorem triangle_finding_lower_bound : ∃ c : ℝ, ∃ N₀ : ℕ, 0 < c ∧
    ∀ N : ℕ, N₀ ≤ N →
      ∀ (t : ℕ) (W : Type) [Fintype W] [DecidableEq W]
        (A : QAlgorithms.QueryAlg (Fin N × Fin N) Bool W t)
        (out : ((Fin N × Fin N) × Bool) × W → TriangleOutput N),
        (∀ x : Edge (⊤ : SimpleGraph (Fin N)) → Bool,
          (∃ o, ValidTriangle ⊤ x o) → (2 : ℝ) / 3 ≤ triangleSuccess ⊤ x A out) →
        c * (N : ℝ) ^ (13 / 12 : ℝ) ≤ (t : ℝ) := by sorry

end QuantumTriangleFinding.Search
