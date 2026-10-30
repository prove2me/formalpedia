-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulation_extension__p2m_c18646d9_4532_475f_9987_0b2cce81491a_a1
-- name    : WilliamsonShmoys.drawable_graph_has_triangulation_extension__p2m_c18646d9_4532_475f_9987_0b2cce81491a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:52:16.868998+00:00
-- url     : https://prove2.me/theorems/20afdcd4-5dba-470f-a57a-287711f6e0ce
-- title:
--   Drawable graph triangulation extension
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulation_extension__p2m_c18646d9_4532_475f_9987_0b2cce81491a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧ L ≤ M ∧
        3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
