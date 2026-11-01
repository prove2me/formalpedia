-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_has_maximal_extension__p2m_c3b679a7_5abb_4fff_8dba_61888269c901_a1
-- name    : WilliamsonShmoys.drawable_supergraph_has_maximal_extension__p2m_c3b679a7_5abb_4fff_8dba_61888269c901_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:48:04.891332+00:00
-- url     : https://prove2.me/theorems/d6f7e1bf-93d3-4723-9af3-e67db3bac663
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every finite graph with a crossing-free drawing has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_has_maximal_extension__p2m_c3b679a7_5abb_4fff_8dba_61888269c901_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
