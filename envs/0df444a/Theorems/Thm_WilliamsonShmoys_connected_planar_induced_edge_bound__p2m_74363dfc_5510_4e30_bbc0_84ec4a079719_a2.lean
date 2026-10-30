-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_induced_edge_bound__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
-- name    : WilliamsonShmoys.connected_planar_induced_edge_bound__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:03.171174+00:00
-- url     : https://prove2.me/theorems/8e79e615-ce68-4197-8611-7fa93173a04e
-- title:
--   Connected planar graph edge bound
-- statement:
--   Bound the edge count of a finite connected graph with a crossing-free drawing by max(1, 3|V|−6). This isolates the topological core used by the parent. For at least three vertices, prove the bound from Euler’s formula and the fact that every face boundary has length at least three in a simple connected planar graph; handle one and two vertices directly. The maximum preserves the valid bounds at those small sizes, including the one-edge graph on two vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_induced_edge_bound__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card <= max 1 (3 * Fintype.card V - 6)) := by
  sorry
