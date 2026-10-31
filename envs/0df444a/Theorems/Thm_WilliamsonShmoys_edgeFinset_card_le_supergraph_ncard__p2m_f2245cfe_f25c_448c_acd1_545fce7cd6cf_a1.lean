-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
-- name    : WilliamsonShmoys.edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:20:42.494509+00:00
-- url     : https://prove2.me/theorems/8600ca9e-9534-46a9-9b62-958cc3f0c9d9
-- title:
--   Subgraph edgeFinset cardinality is bounded by supergraph edge count
-- statement:
--   If G is a subgraph of H, the cardinality of G's edgeFinset is at most H's edgeSet cardinality. A proof can identify the finite edgeFinset cardinality with G.edgeSet.ncard and use edge-set inclusion. The explicit decidable adjacency instance matches the target's local instance; no positivity or nonempty-graph assumption is needed, so the empty graph is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card) ≤ H.edgeSet.ncard := by sorry
