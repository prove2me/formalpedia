-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bounds__p2m_13cac36b_d337_49ef_981f_d43d139f211c_a2
-- name    : WilliamsonShmoys.connected_planar_edge_bounds__p2m_13cac36b_d337_49ef_981f_d43d139f211c_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:58:52.28851+00:00
-- url     : https://prove2.me/theorems/961b854d-f4cc-4b36-ad05-39668b153494
-- title:
--   Connected planar graph edge bounds
-- statement:
--   For a finite connected simple graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn`, the vertex count is at most one more than the edge count, and the edge count plus six is at most three times the vertex count. The connected bound follows from a spanning tree. The planar bound follows from Euler’s formula and counting incidences along facial boundary walks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bounds__p2m_13cac36b_d337_49ef_981f_d43d139f211c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Fintype.card V ≤ K.edgeFinset.card + 1 ∧
      K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
