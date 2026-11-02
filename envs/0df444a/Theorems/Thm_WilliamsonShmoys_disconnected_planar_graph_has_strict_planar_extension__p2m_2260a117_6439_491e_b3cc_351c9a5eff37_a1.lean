-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_strict_planar_extension__p2m_2260a117_6439_491e_b3cc_351c9a5eff37_a1
-- name    : WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension__p2m_2260a117_6439_491e_b3cc_351c9a5eff37_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:40:17.240894+00:00
-- url     : https://prove2.me/theorems/e7f58e98-9faf-49a6-bc58-50960cb4a0da
-- title:
--   A disconnected planar drawing has a strict planar extension
-- statement:
--   Given a disconnected simple graph on at least three vertices with a drawing satisfying HasPlanarDrawingOn, there is a strictly larger simple graph on the same vertices that also has such a drawing. The intended geometric argument joins exposed vertices from distinct components through the unbounded face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension__p2m_2260a117_6439_491e_b3cc_351c9a5eff37_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hDisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K ≠ G := by
  sorry
