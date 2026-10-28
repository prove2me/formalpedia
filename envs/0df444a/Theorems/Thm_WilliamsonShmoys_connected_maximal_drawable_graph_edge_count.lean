-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_maximal_drawable_graph_edge_count
-- name    : WilliamsonShmoys.connected_maximal_drawable_graph_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:54:30.252353+00:00
-- url     : https://prove2.me/theorems/21f4c78e-28c3-4c5f-ad00-babc83b9505c
-- title:
--   Edge count of a connected maximal drawable graph
-- statement:
--   A connected drawable simple graph on at least three vertices that admits no drawable edge extension has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_maximal_drawable_graph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Q.Connected)
    (hmax : ∀ M : SimpleGraph V,
      Q ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M ≤ Q) :
    3 * Fintype.card V - 6 = Q.edgeSet.ncard := by sorry
