-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_fixed_graph_triangle_search
-- name    : QuantumTriangleFinding.Search.fixed_graph_triangle_search
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:22.892942+00:00
-- url     : https://prove2.me/theorems/535a122c-160d-4246-8065-dbc1258d7cf2
-- title:
--   Theorem 5.1 — Triangle search in a fixed graph
-- statement:
--   There are absolute constants $C_0,C_1>0$ such that the following holds for every finite simple undirected known host $G$, with $m$ edges, maximum degree $\Delta$ and $M\ge1$ triangles. If
--   $$0<p\le\frac1{10\sqrt\Delta},\qquad \Delta p\ge C_0\log(2m),$$
--   then every $t$-query quantum algorithm has actual average triangle-search success $\sigma$ under the uniform mixture of individually conditioned unique-triangle laws bounded by
--   $$\sqrt\sigma\le C_1(t+3)\frac{\Delta^{1/3}}{\sqrt M\,p^{1/6}}.$$
--   The constants precede the graph, density, horizon, ancillary workspace, circuit and decoder. No pointwise or average success hypothesis is imposed. The algorithm may query all adjacency pairs, and receives no planted-triangle label. This preserves the full domain and exponent of the fixed-host result.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected hosts and three-edge triangles → SimpleGraph (Fin N), sorted endpoint pairs and unordered three-vertex cliques; circuits may query every ordered vertex pair; reason: finite relabeling and the vertex-set/edge-set correspondence preserve every instance; loops and host nonedges return zero and both edge orientations agree
--   - encoding: arbitrary final measurements in the purified finite quantum query model → published QueryAlg circuits with arbitrary finite ancillas, input-independent final unitaries and basis-output decoders; reason: finite coherent measurement dilation represents every source algorithm with the same query count; starts, gates and decoders are fixed before the oracle input
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Theorem 5.1, (5.1)–(5.2), p. 25; positive law, pp. 25–26

import Definitions.Def_QuantumTriangleFinding_Search_GraphModel

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Theorem 5.1, p.25: C₀,C₁ precede the host, density, horizon and all algorithms. -/
theorem fixed_graph_triangle_search : ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (p : ℝ),
      1 ≤ triangleCount G → 0 < p →
      p ≤ 1 / (10 * Real.sqrt (maxDegree G : ℝ)) →
      C₀ * Real.log (2 * (edgeCount G : ℝ)) ≤ (maxDegree G : ℝ) * p →
      ∀ (t : ℕ) (W : Type) [Fintype W] [DecidableEq W]
        (A : QAlgorithms.QueryAlg (Fin N × Fin N) Bool W t)
        (out : ((Fin N × Fin N) × Bool) × W → TriangleOutput N),
        Real.sqrt (averageTriangleSuccess G p A out) ≤
          C₁ * ((t : ℝ) + 3) * (maxDegree G : ℝ) ^ (1 / 3 : ℝ) /
            (Real.sqrt (triangleCount G : ℝ) * p ^ (1 / 6 : ℝ)) := by sorry

end QuantumTriangleFinding.Search
