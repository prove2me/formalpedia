-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_simple_edge_bound__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1
-- name    : WilliamsonShmoys.connected_planar_simple_edge_bound__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:45:41.801532+00:00
-- url     : https://prove2.me/theorems/203b6e6b-f468-4fb9-a6ed-110500d4f041
-- title:
--   Simple planar edge bound
-- statement:
--   A connected simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_simple_edge_bound__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) (hConnected : G.Connected) (hCard : 3 <= Fintype.card V) : G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
