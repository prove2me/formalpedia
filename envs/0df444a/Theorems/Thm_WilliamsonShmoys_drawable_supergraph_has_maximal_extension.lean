-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_has_maximal_extension
-- name    : WilliamsonShmoys.drawable_supergraph_has_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:56:47.841365+00:00
-- url     : https://prove2.me/theorems/98628b85-0343-4484-860c-e3513cb03d17
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_supergraph_has_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K := by sorry
