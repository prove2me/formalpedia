-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_graph_euler_faces
-- name    : WilliamsonShmoys.connected_planar_graph_euler_faces
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:09:11.42968+00:00
-- url     : https://prove2.me/theorems/e061faf9-e45d-466a-ba40-a3ddc643663c
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with a drawing satisfying HasPlanarDrawingOn has a natural-number face count F satisfying Euler’s formula |V| + F = |E| + 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.connected_planar_graph_euler_faces
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ F : ℕ, Fintype.card V + F = Y.edgeSet.ncard + 2 := by sorry
