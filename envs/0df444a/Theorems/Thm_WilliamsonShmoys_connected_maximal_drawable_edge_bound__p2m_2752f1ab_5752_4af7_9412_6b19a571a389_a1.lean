-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_maximal_drawable_edge_bound__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1
-- name    : WilliamsonShmoys.connected_maximal_drawable_edge_bound__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:53:29.177965+00:00
-- url     : https://prove2.me/theorems/0e666a95-297a-413c-b595-00fce77573e5
-- title:
--   Edge bound for a connected maximal drawable graph
-- statement:
--   A connected drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_maximal_drawable_edge_bound__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (dM : DecidableRel M.Adj) (hM : HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) (hmax : forall (N : SimpleGraph V) (dN : DecidableRel N.Adj), M <= N -> HasPlanarDrawingOn N -> N = M) (hconn : M.Connected) : 3 * Fintype.card V <= M.edgeFinset.card + 6 := by sorry
