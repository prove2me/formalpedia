-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawable_graph_has_strict_drawable_extension__p2m_edef7c40_3af7_4dfb_a988_ccba8165ed88_a1
-- name    : WilliamsonShmoys.disconnected_drawable_graph_has_strict_drawable_extension__p2m_edef7c40_3af7_4dfb_a988_ccba8165ed88_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:39:35.943593+00:00
-- url     : https://prove2.me/theorems/41ac2ad2-1442-40d5-933f-adb24d67ad24
-- title:
--   A disconnected drawable graph has a strict drawable extension
-- statement:
--   For a finite ordered vertex type with at least three vertices, any drawable disconnected graph has a strictly larger drawable graph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawable_graph_has_strict_drawable_extension__p2m_edef7c40_3af7_4dfb_a988_ccba8165ed88_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ L.Connected) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧ L ≤ M ∧ L ≠ M := by sorry
