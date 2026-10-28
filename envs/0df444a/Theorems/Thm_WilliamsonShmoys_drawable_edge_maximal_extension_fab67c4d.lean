-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_edge_maximal_extension_fab67c4d
-- name    : WilliamsonShmoys.drawable_edge_maximal_extension_fab67c4d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:22:54.148977+00:00
-- url     : https://prove2.me/theorems/8787ee1d-7efc-4098-888c-60bc1410c260
-- title:
--   Finite drawable edge maximal extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable edge supergraph on that same vertex type that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_edge_maximal_extension_fab67c4d
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L.edgeSet ⊂ M.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
