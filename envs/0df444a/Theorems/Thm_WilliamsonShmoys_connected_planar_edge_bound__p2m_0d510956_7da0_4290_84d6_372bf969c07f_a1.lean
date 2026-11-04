-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:00:21.001272+00:00
-- url     : https://prove2.me/theorems/6dc85c3d-85f5-4b78-a1c3-d13b079de4de
-- title:
--   Connected planar simple graph edge bound
-- statement:
--   A finite connected simple graph on at least three vertices with a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) (hconn : M.Connected) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card + 6 <= 3 * Fintype.card V) := by sorry
