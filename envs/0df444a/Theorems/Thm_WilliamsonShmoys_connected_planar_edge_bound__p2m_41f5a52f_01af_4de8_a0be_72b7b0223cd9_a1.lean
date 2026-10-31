-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_41f5a52f_01af_4de8_a0be_72b7b0223cd9_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_41f5a52f_01af_4de8_a0be_72b7b0223cd9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:53:43.516429+00:00
-- url     : https://prove2.me/theorems/8c4c2f22-8a29-4bb9-b6b3-bc1cdb27cdf5
-- title:
--   Euler edge bound for connected drawn simple graphs
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges. Derive this from a planar embedding, Euler’s formula, and the fact that each face boundary has length at least three in this size range. The size condition excludes the one-edge connected graph, whose unique facial boundary walk can have length two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_41f5a52f_01af_4de8_a0be_72b7b0223cd9_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hconn : K.Connected) (hdraw : HasPlanarDrawingOn K) (hV : 3 <= Fintype.card V) : K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
