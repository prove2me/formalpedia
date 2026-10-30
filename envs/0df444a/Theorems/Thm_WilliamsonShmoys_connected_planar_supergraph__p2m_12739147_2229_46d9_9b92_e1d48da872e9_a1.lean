-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1
-- name    : WilliamsonShmoys.connected_planar_supergraph__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:55:32.748361+00:00
-- url     : https://prove2.me/theorems/d3d31f3d-a307-414d-b52d-807cd959ed73
-- title:
--   Connect a drawable graph by adding drawable edges
-- statement:
--   Every graph with a crossing-free drawing has a connected drawable supergraph on the same finite ordered vertex type. This removes the disconnected case from the parent proof. A proof route is to join distinct drawing components through the complement of the drawing, adding arcs until the graph is connected; each new arc connects components and can be chosen without crossing existing edges. This geometric construction is the remaining obligation of this child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_supergraph__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
