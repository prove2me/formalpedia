-- Prove2me | Theorems.Thm_WilliamsonShmoys_connect_planar_drawing__p2m_2ba654e2_e4e9_4dba_a1f5_978037f8b005_a2
-- name    : WilliamsonShmoys.connect_planar_drawing__p2m_2ba654e2_e4e9_4dba_a1f5_978037f8b005_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:52:49.167982+00:00
-- url     : https://prove2.me/theorems/dedac0bb-90f3-4248-aa67-375db03efa3d
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Extend the given drawing to a connected graph on the same finite vertex type, keeping all original edges and retaining a crossing-free drawing. The vertex-count hypothesis rules out small exceptional cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys

theorem WilliamsonShmoys.connect_planar_drawing__p2m_2ba654e2_e4e9_4dba_a1f5_978037f8b005_a2 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S) (hV : 3 <= Fintype.card V) : ∃ T : SimpleGraph V, S.edgeSet.ncard <= T.edgeSet.ncard ∧ HasPlanarDrawingOn T ∧ T.Connected := by sorry
