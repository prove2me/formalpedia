-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension_f1f92bb7_maximal_supergraph_edge_count
-- name    : WilliamsonShmoys.drawable_triangulation_extension_f1f92bb7_maximal_supergraph_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:26:03.800081+00:00
-- url     : https://prove2.me/theorems/eccbc3ea-a49b-47f0-9f72-4d134a188e7f
-- title:
--   Edge count of a maximal drawable supergraph
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_triangulation_extension_f1f92bb7_maximal_supergraph_edge_count {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) (hCard : 3 ≤ Fintype.card V) : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
