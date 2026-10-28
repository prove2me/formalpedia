-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_counts_v2
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_counts_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:10:11.100833+00:00
-- url     : https://prove2.me/theorems/2215f4a6-abc8-46a4-8daa-6b014a3b506a
-- title:
--   Euler and face-degree counts for a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing, there is a natural face count satisfying Euler's equation and the total face-boundary degree inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler_counts_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * L.edgeSet.ncard := by sorry
