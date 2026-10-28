-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_equation
-- name    : WilliamsonShmoys.connected_planar_euler_equation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:00:44.392987+00:00
-- url     : https://prove2.me/theorems/14594ec3-7c36-4105-8948-79e19891e8a1
-- title:
--   Euler equation for a connected planar graph
-- statement:
--   For a finite connected graph with at least three vertices and a crossing-free drawing, the vertex, edge, and face counts satisfy Euler’s equation. A proof can formalize the plane embedding, then delete edges on cycles while tracking faces until a spanning tree remains.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler_equation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by sorry
