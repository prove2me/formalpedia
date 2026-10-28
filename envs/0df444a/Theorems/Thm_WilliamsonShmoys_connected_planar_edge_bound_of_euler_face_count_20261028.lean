-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_of_euler_face_count_20261028
-- name    : WilliamsonShmoys.connected_planar_edge_bound_of_euler_face_count_20261028
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:08:41.269464+00:00
-- url     : https://prove2.me/theorems/c4592f6f-2a9f-4790-8858-9196a8ab895b
-- title:
--   Planar edge bound from Euler face count
-- statement:
--   Euler’s equation and the aggregate facial-boundary inequality imply the standard `3|V| - 6` edge bound when there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_of_euler_face_count_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (F : ℕ)
    (hEuler : Fintype.card V + F = G.edgeSet.ncard + 2)
    (hFaces : 3 * F ≤ 2 * G.edgeSet.ncard) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
