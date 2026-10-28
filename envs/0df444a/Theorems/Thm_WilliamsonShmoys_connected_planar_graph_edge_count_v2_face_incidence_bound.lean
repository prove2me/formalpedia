-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_count_v2_face_incidence_bound
-- name    : WilliamsonShmoys.connected_planar_graph_edge_count_v2_face_incidence_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:15:40.652899+00:00
-- url     : https://prove2.me/theorems/8b6bc1d0-8ae3-4194-b54a-dbb7d52694ad
-- title:
--   Face incidence bound for the connected planar drawing edge bound
-- statement:
--   For a connected simple graph with at least three vertices and the supplied planar drawing, a face count satisfying Euler’s relation obeys `3f ≤ 2|E|`. A proof route is to count face-boundary incidences: each edge contributes two, and each face has at least three. Simplicity rules out a boundary of length one; connectedness together with the vertex lower bound rules out a boundary of length two, including the bridge-only boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_graph_edge_count_v2_face_incidence_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (f : ℕ)
    (hEuler : Fintype.card V + f = Y.edgeSet.ncard + 2) :
    3 * f ≤ 2 * Y.edgeSet.ncard := by sorry
