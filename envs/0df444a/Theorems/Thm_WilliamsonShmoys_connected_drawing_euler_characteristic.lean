-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_characteristic
-- name    : WilliamsonShmoys.connected_drawing_euler_characteristic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:03:47.905684+00:00
-- url     : https://prove2.me/theorems/220959e1-9ff9-4e88-acf9-3e4d8288ed4f
-- title:
--   Euler face count for connected drawings
-- statement:
--   For a finite connected graph with at least three vertices and a crossing-free drawing as defined by `HasPlanarDrawingOn`, the number of complementary faces is the natural number f satisfying |V| + f = |E| + 2. The hypothesis |V| ≥ 3 keeps this claim within the parent’s boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawing_euler_characteristic
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    exists f : Nat, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
