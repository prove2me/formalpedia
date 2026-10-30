-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_for_certificate_38ffb807
-- name    : WilliamsonShmoys.connected_planar_edge_bound_for_certificate_38ffb807
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:00:00.808695+00:00
-- url     : https://prove2.me/theorems/2e218f84-656e-466a-a3a9-bc8a6a06da0b
-- title:
--   Euler edge bound for a connected drawn simple graph
-- statement:
--   A connected simple graph on at least three vertices with a crossing-free drawing has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound_for_certificate_38ffb807
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
