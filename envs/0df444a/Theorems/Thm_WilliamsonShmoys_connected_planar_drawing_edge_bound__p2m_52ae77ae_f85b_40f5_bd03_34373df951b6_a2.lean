-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:47:48.939236+00:00
-- url     : https://prove2.me/theorems/044c324d-acb7-4615-b70a-8b8b8a044876
-- title:
--   Edge bound for connected drawn planar graphs
-- statement:
--   This new lemma isolates the main topological work: the connected case of the target. Convert the supplied drawing into its plane embedding, use Euler’s formula V − E + F = 2, and count face-edge incidences. Each edge has two sides, and for a connected simple graph with at least three vertices each facial boundary walk has length at least three; thus 3F ≤ 2E, yielding E + 6 ≤ 3V. The connectedness, simplicity, and vertex-count hypotheses are retained to exclude the exceptional small facial walks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
