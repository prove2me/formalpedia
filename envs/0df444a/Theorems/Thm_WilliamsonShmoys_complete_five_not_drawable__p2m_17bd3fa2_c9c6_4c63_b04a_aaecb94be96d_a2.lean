-- Prove2me | Theorems.Thm_WilliamsonShmoys_complete_five_not_drawable__p2m_17bd3fa2_c9c6_4c63_b04a_aaecb94be96d_a2
-- name    : WilliamsonShmoys.complete_five_not_drawable__p2m_17bd3fa2_c9c6_4c63_b04a_aaecb94be96d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:58:12.065151+00:00
-- url     : https://prove2.me/theorems/2bc0f91b-8c97-4ed0-8294-73ad2db6cdd7
-- title:
--   The complete graph on five vertices has no planar drawing
-- statement:
--   Any simple graph on five vertices containing every edge between distinct vertices has no drawing under the project's definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.complete_five_not_drawable__p2m_17bd3fa2_c9c6_4c63_b04a_aaecb94be96d_a2 :
    ∀ M : SimpleGraph (Fin 5),
      (∀ i j : Fin 5, i ≠ j → M.Adj i j) →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
