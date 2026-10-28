-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_extension
-- name    : WilliamsonShmoys.drawable_supergraph_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:45:34.260395+00:00
-- url     : https://prove2.me/theorems/7bf02ea9-06d0-4dfc-9d99-220babc0fb21
-- title:
--   Maximal drawable extension on a finite vertex set
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
