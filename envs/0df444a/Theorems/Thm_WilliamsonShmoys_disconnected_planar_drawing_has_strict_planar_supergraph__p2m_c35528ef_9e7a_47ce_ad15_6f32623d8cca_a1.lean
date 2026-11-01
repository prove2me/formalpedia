-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_strict_planar_supergraph__p2m_c35528ef_9e7a_47ce_ad15_6f32623d8cca_a1
-- name    : WilliamsonShmoys.disconnected_planar_drawing_has_strict_planar_supergraph__p2m_c35528ef_9e7a_47ce_ad15_6f32623d8cca_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:13:53.750881+00:00
-- url     : https://prove2.me/theorems/3b771bff-ba9c-4fe2-a9ff-31debf5be919
-- title:
--   A disconnected planar drawing has a strict drawable supergraph
-- statement:
--   Every disconnected graph with a crossing-free drawing on the given finite ordered vertex type has a strictly larger supergraph on that same type that also has such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_planar_drawing_has_strict_planar_supergraph__p2m_c35528ef_9e7a_47ce_ad15_6f32623d8cca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hdis : ¬ M.Connected) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ N ≠ M := by sorry
