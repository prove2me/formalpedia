-- Prove2me | Theorems.Thm_WilliamsonShmoys_SimpleGraph_edge_card_mono_and_eq_of_le__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
-- name    : WilliamsonShmoys.SimpleGraph.edge_card_mono_and_eq_of_le__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:48:09.78748+00:00
-- url     : https://prove2.me/theorems/55033ca9-d7d4-4a46-90f3-569cdc090007
-- title:
--   Edge count detects equality under graph inclusion
-- statement:
--   For finite-vertex simple graphs, inclusion implies edge-count monotonicity, and inclusion together with the reverse edge-count inequality implies graph equality. In the parent, this proves that H has no more edges than the chosen supergraph K, and that any drawable L extending K with no greater edge count must equal K. A proof route uses inclusion of edge finsets, monotonicity of finite-set cardinality, and equality of finite sets with equal cardinality under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.SimpleGraph.edge_card_mono_and_eq_of_le__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel H.Adj := Classical.decRel H.Adj
     G.edgeFinset.card ≤ H.edgeFinset.card ∧
       (H.edgeFinset.card ≤ G.edgeFinset.card → G = H)) := by sorry
