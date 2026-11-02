-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_induced_planar_edge_count_upper__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1
-- name    : WilliamsonShmoys.connected_induced_planar_edge_count_upper__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:26:11.499539+00:00
-- url     : https://prove2.me/theorems/488e10ca-0ab9-4c81-afb8-1721f455ea05
-- title:
--   Edge bound for connected induced subgraphs of a planar drawing
-- statement:
--   Any induced subgraph on at least three vertices that is connected inherits a crossing-free drawing and has at most three times its vertex count minus six edges. Prove by restricting the supplied drawing and applying Euler's formula and the face-degree bound for a simple connected planar graph. This removes the topological counting work from the parent; the Euler argument remains the main core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_induced_planar_edge_count_upper__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (s : Finset V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ s.card)
    (hconn : (H.induce (↑s : Set V)).Connected) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    (H.induce (↑s : Set V)).edgeFinset.card ≤ 3 * s.card - 6 := by sorry
