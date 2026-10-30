-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_strictly_more_edges__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
-- name    : WilliamsonShmoys.connected_strictly_more_edges__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:52.166205+00:00
-- url     : https://prove2.me/theorems/aa1c0f88-12e6-45d6-95aa-86e230dae063
-- title:
--   Connected extension strictly increases edge count
-- statement:
--   A connected simple graph extension of a disconnected finite simple graph has strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_strictly_more_edges__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1 {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) (hKH : K ≤ H)
    (hK : ¬ K.Connected) (hH : H.Connected) :
    K.edgeSet.ncard < H.edgeSet.ncard := by sorry
