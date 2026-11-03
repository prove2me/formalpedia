-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulation_extension__p2m_5f13f5bc_06ce_43c4_9feb_29baebe6cd36_a2
-- name    : WilliamsonShmoys.drawable_graph_has_triangulation_extension__p2m_5f13f5bc_06ce_43c4_9feb_29baebe6cd36_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:42:54.773196+00:00
-- url     : https://prove2.me/theorems/ee01e952-1ee0-4062-a12a-4c7920469f52
-- title:
--   Drawable graph has an exact edge-count triangulation extension
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex set with at least three vertices is contained in a drawable graph on the same vertices whose edge count is exactly three times the vertex count minus six. The extension includes an explicit decidability instance for its adjacency relation so its finite edge count is defined.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulation_extension__p2m_5f13f5bc_06ce_43c4_9feb_29baebe6cd36_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : HasPlanarDrawingOn G) (hcard : 3 <= Fintype.card V) : Exists fun M : SimpleGraph V => Exists fun hDec : DecidableRel M.Adj => letI : DecidableRel M.Adj := hDec; G <= M /\ HasPlanarDrawingOn M /\ 3 * Fintype.card V = M.edgeFinset.card + 6 := by sorry
