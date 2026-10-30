-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_connected_supergraph_strict__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
-- name    : WilliamsonShmoys.disconnected_connected_supergraph_strict__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:14.131403+00:00
-- url     : https://prove2.me/theorems/061038f3-e4d7-4190-bc3f-1b77ac22688d
-- title:
--   A connected supergraph strictly enlarges a disconnected graph
-- statement:
--   If `H` is an edge-subgraph of connected `K` and `H` is disconnected, then the edge inclusion is strict. Equality of edge finsets would imply equality of the graphs and transfer connectedness to `H`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.disconnected_connected_supergraph_strict__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H.edgeFinset ⊆ K.edgeFinset)
    (hH : ¬ H.Connected)
    (hK : K.Connected) :
    H.edgeFinset ⊂ K.edgeFinset := by sorry
