-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_edge_count__p2m_7d22c919_3efe_4469_8040_ed9baa851075_a1
-- name    : WilliamsonShmoys.drawable_triangulation_edge_count__p2m_7d22c919_3efe_4469_8040_ed9baa851075_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:34:02.632225+00:00
-- url     : https://prove2.me/theorems/f8a91428-e2c7-41b2-beea-f098a7f4c4b7
-- title:
--   Extend a planar drawing to a triangulation with the Euler edge count
-- statement:
--   Any planar drawing on at least three vertices can be extended, without changing its vertex set, to a drawable graph whose faces are triangular and whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_triangulation_edge_count__p2m_7d22c919_3efe_4469_8040_ed9baa851075_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      N.edgeFinset ⊆ K.edgeFinset ∧
      K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
