-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_maximal_extension__p2m_c603be23_9a74_4dd9_9858_66dd86a4b903_a1
-- name    : WilliamsonShmoys.drawable_graph_maximal_extension__p2m_c603be23_9a74_4dd9_9858_66dd86a4b903_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:20:56.41261+00:00
-- url     : https://prove2.me/theorems/f01cdcae-4c5c-4ee7-9874-f56857bf541e
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Any drawable finite simple graph has a drawable supergraph on the same vertex set that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_maximal_extension__p2m_c603be23_9a74_4dd9_9858_66dd86a4b903_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by sorry
