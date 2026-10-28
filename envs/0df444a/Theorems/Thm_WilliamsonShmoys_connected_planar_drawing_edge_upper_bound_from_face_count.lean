-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_upper_bound_from_face_count
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_from_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:58:24.854502+00:00
-- url     : https://prove2.me/theorems/b977ac3e-5faf-4d79-9f24-345f1207e0b5
-- title:
--   Derive the planar edge bound from face counts
-- statement:
--   Natural-number vertex, edge, and face counts satisfying Euler’s relation and the face-boundary inequality imply the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_from_face_count
    (v e f : ℕ) (hv : 3 <= v)
    (hEuler : v + f = e + 2)
    (hFaces : 3 * f <= 2 * e) :
    e + 6 <= 3 * v := by sorry
