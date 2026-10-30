-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_has_triangulated_edge_count_certificate
-- name    : WilliamsonShmoys.drawing_has_triangulated_edge_count_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:31:45.287996+00:00
-- url     : https://prove2.me/theorems/92c8f67c-2acf-4978-9513-2ea87c7b1443
-- title:
--   Triangulated supergraph certificate for a planar drawing
-- statement:
--   A finite simple graph on at least three vertices with a crossing-free drawing has a connected triangulated planar supergraph on the same vertices. If that supergraph has m edges and f faces, its edge count bounds the original graph’s, Euler’s relation gives n + f = m + 2, and its face boundaries give 3f ≤ 2m.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawing_has_triangulated_edge_count_certificate {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : ∃ m f : Nat, G.edgeSet.ncard ≤ m ∧ Fintype.card V + f = m + 2 ∧ 3 * f ≤ 2 * m := by sorry
