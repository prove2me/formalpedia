-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_inequality
-- name    : WilliamsonShmoys.connected_planar_euler_face_inequality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:48:55.780209+00:00
-- url     : https://prove2.me/theorems/dd6acdd1-4a1c-4f79-9506-af44b9d3a7fb
-- title:
--   Euler face count and degree bound for connected planar graphs
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free plane drawing has a natural-number face count f satisfying Euler’s formula and the total face-boundary degree inequality. The parent combines these facts arithmetically to obtain the edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler_face_inequality
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hPconn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = P.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * P.edgeSet.ncard := by sorry
