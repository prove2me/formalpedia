-- Prove2me | Theorems.Thm_WilliamsonShmoys_cut_implies_not_reachable__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a3
-- name    : WilliamsonShmoys.cut_implies_not_reachable__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:17:37.350992+00:00
-- url     : https://prove2.me/theorems/522fcb48-849e-434e-80b2-a38f08520ee6
-- title:
--   An edge-free cut separates its sides
-- statement:
--   If every edge crossing from a set of vertices to its complement is forbidden, then a vertex in the set cannot be reachable from a vertex outside it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.cut_implies_not_reachable__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {u v : V} (A : Set V)
    (huA : u ∈ A) (hvA : v ∉ A)
    (hcut : ∀ {x y : V}, x ∈ A → y ∉ A → ¬ G.Adj x y) :
    ¬ G.Reachable u v := by sorry
