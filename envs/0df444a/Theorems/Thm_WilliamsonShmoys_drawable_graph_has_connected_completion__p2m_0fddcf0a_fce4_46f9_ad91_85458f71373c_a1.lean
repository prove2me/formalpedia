-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_connected_completion__p2m_0fddcf0a_fce4_46f9_ad91_85458f71373c_a1
-- name    : WilliamsonShmoys.drawable_graph_has_connected_completion__p2m_0fddcf0a_fce4_46f9_ad91_85458f71373c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:51:13.347787+00:00
-- url     : https://prove2.me/theorems/89476783-ab1a-4442-845c-f76f70f7bf06
-- title:
--   Connect components of a drawable graph
-- statement:
--   Any drawable finite graph on at least three vertices has a connected drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_connected_completion__p2m_0fddcf0a_fce4_46f9_ad91_85458f71373c_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by sorry
