-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_maximal_extension__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
-- name    : WilliamsonShmoys.drawable_triangulation_maximal_extension__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:07:01.259982+00:00
-- url     : https://prove2.me/theorems/2dea5b09-c429-4a5e-b3c1-b82fac24916e
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Any drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_triangulation_maximal_extension__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by sorry
