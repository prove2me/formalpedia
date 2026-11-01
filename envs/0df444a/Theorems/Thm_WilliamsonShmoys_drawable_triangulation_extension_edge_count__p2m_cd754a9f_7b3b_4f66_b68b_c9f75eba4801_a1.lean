-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension_edge_count__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a1
-- name    : WilliamsonShmoys.drawable_triangulation_extension_edge_count__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:15:29.963021+00:00
-- url     : https://prove2.me/theorems/5303ee26-08e8-4d11-9742-cd82622b8993
-- title:
--   Drawable graphs extend to the planar edge lower bound
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type whose edge count is at least 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_triangulation_extension_edge_count__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (N : SimpleGraph V), M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∃ (dN : DecidableRel N.Adj),
        (letI : DecidableRel N.Adj := dN
         3 * Fintype.card V - 6 ≤ N.edgeFinset.card) := by
  sorry
