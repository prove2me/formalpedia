-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_from_embedding
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_from_embedding
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:14:21.738021+00:00
-- url     : https://prove2.me/theorems/d975caed-e731-43b9-a69a-20b678db2487
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with a crossing-free drawing has a natural-number face count satisfying Euler’s relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler_from_embedding
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G) :
    ∃ f : ℕ, G.edgeSet.ncard + 2 = Fintype.card V + f := by sorry
