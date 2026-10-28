-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawingOn_euler
-- name    : WilliamsonShmoys.drawingOn_euler
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:09:19.811997+00:00
-- url     : https://prove2.me/theorems/59df8e05-51b7-44b9-b544-841d98a71c24
-- title:
--   Euler relation for a connected graph drawing
-- statement:
--   A connected finite graph with the supplied planar drawing has a natural-number face count satisfying Euler’s relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.drawingOn_euler {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
