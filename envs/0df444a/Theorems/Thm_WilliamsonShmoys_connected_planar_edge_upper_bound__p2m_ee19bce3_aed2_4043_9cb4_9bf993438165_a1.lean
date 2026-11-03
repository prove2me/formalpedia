-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
-- name    : WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:07:40.657545+00:00
-- url     : https://prove2.me/theorems/f073101b-bf91-4d7c-9d90-d062f14a8fca
-- title:
--   Connected planar graph Euler edge bound
-- statement:
--   A connected simple graph with at least three vertices and a drawing satisfying the supplied crossing-free arc conditions has at most three times its number of vertices minus six edges. This is the topological core: derive Euler’s formula for the embedding, count edge-face incidences, and use that each face boundary has length at least three under these size and simplicity hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hconn : G.Connected) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
