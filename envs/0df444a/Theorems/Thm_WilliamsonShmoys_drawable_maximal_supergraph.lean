-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_maximal_supergraph
-- name    : WilliamsonShmoys.drawable_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:38:01.246427+00:00
-- url     : https://prove2.me/theorems/82754507-818c-4549-b011-cde58d548ee0
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V, T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
      ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ U := by sorry
