-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:01:40.515991+00:00
-- url     : https://prove2.me/theorems/9ccf8ab9-0495-4b50-8b51-030e6fe4c678
-- title:
--   Connected planar graph edge bound
-- statement:
--   This child handles the connected case. It preserves the three-vertex lower bound, including the sharp three-vertex boundary case. Starting from the given drawing, the proof route is to derive the planar embedding's Euler relation, count face-boundary incidences, use that every face boundary has length at least three for a simple connected graph with at least three vertices, and conclude the edge inequality. This removes the Euler and face-counting argument from the parent; that topological formalization is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConnected : H.Connected) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
