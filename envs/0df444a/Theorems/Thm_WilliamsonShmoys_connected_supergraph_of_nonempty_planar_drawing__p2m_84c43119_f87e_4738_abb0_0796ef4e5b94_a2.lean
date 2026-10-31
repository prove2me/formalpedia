-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_supergraph_of_nonempty_planar_drawing__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
-- name    : WilliamsonShmoys.connected_supergraph_of_nonempty_planar_drawing__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:49:55.486027+00:00
-- url     : https://prove2.me/theorems/f78c47b9-d868-40e5-8e8a-074adc9ccdd0
-- title:
--   Connect a planar drawing with at least three vertices
-- statement:
--   A graph with a crossing-free drawing and at least three vertices has a connected supergraph on the same vertex set that also has a crossing-free drawing, with no fewer edges. The cardinality hypothesis excludes the empty-type counterexample to the earlier version. Prove this by joining drawing components one at a time with arcs through the complement; inclusion of edge sets gives the edge-count inequality. This isolates the geometric component-joining step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_supergraph_of_nonempty_planar_drawing__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧ H.edgeSet.ncard ≤ G.edgeSet.ncard := by sorry
