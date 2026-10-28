-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_augmentation
-- name    : WilliamsonShmoys.connected_planar_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:26:25.729517+00:00
-- url     : https://prove2.me/theorems/203d0297-90ce-4966-88c7-7e4da21e2c91
-- title:
--   Connected planar augmentation on the same vertices
-- statement:
--   Any graph on at least three vertices with the given crossing-free drawing can be extended, on the same vertex type, to a connected graph with a crossing-free drawing, without removing edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_planar_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
