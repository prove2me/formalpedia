-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_induced_bound_of_drawing__p2m_a0486957_c188_41a2_adb4_3f006dabe729_a2
-- name    : WilliamsonShmoys.connected_induced_bound_of_drawing__p2m_a0486957_c188_41a2_adb4_3f006dabe729_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:47:50.74444+00:00
-- url     : https://prove2.me/theorems/7740fad9-b291-4e49-8381-e83e61d59ffd
-- title:
--   Edge bound for connected induced subgraphs of a drawn graph
-- statement:
--   Every induced subgraph on at least three vertices that is connected inherits the planar edge bound from the drawing of the full graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_induced_bound_of_drawing__p2m_a0486957_c188_41a2_adb4_3f006dabe729_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) : ∀ (s : Finset V), 3 ≤ s.card → (K.induce (↑s : Set V)).Connected → (K.induce (↑s : Set V)).edgeSet.ncard + 6 ≤ 3 * s.card := by sorry
