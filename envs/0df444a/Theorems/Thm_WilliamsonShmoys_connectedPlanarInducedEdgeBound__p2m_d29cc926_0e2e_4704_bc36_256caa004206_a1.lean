-- Prove2me | Theorems.Thm_WilliamsonShmoys_connectedPlanarInducedEdgeBound__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
-- name    : WilliamsonShmoys.connectedPlanarInducedEdgeBound__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:43:48.371961+00:00
-- url     : https://prove2.me/theorems/c24b8acc-e048-42e5-be54-b766a7976a06
-- title:
--   Edge bound for a connected planar induced subgraph
-- statement:
--   For any subset of a finite drawn planar graph whose induced subgraph is connected, the number of induced edges plus three is at most three times the subset size, including the one- and two-vertex cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connectedPlanarInducedEdgeBound__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (s : Finset V) (hconn : (L.induce (↑s : Set V)).Connected) :
    (letI : DecidableRel L.Adj := dL
     (L.induce (↑s : Set V)).edgeFinset.card) + 3 ≤ 3 * s.card := by sorry
