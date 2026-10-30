-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound_for_face_inequality
-- name    : WilliamsonShmoys.connected_planar_edge_count_bound_for_face_inequality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:15:22.19225+00:00
-- url     : https://prove2.me/theorems/dac5ce51-df85-4cbe-b21c-c8b2f1840495
-- title:
--   Simple planar edge bound for the face-count inequality
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied crossing-free drawing has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_bound_for_face_inequality
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hPconn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
