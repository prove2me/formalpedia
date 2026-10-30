-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1
-- name    : WilliamsonShmoys.drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:10.95403+00:00
-- url     : https://prove2.me/theorems/936c8f2f-e450-4005-a534-4738c0b76713
-- title:
--   Maximal drawable extension
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex type that is maximal under graph inclusion among drawable supergraphs. The statement has no vertex-count restriction: the finite family of drawable supergraphs is nonempty because it contains G, so an inclusion-maximal member exists. Its proof route is finite maximality, with the drawing predicate carried as the admissibility condition. This removes the choice of a maximal extension from the parent; the remaining core is showing that such an extension has the required edge count, supplied by the other child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧ HasPlanarDrawingOn L ∧
        ∀ H : SimpleGraph V, L ≤ H → HasPlanarDrawingOn H → H = L := by sorry
