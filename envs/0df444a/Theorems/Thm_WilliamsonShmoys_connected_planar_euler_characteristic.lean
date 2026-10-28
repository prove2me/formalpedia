-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_characteristic
-- name    : WilliamsonShmoys.connected_planar_euler_characteristic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:15:00.505518+00:00
-- url     : https://prove2.me/theorems/dbe23106-f197-48e7-b2d2-1d3b2f1777e0
-- title:
--   Euler characteristic of a connected planar drawing
-- statement:
--   For a finite connected graph with the supplied crossing-free drawing, there is a finite number of faces F satisfying Euler’s formula |V| + F = |E| + 2. This is the topological Euler-characteristic step; it applies to trees and graphs with bridges as well as to 2-connected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler_characteristic
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ F : ℕ, Fintype.card V + F = K.edgeSet.ncard + 2 := by sorry
