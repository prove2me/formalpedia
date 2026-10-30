-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_strict_planar_extension_of_three_vertices__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a2
-- name    : WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension_of_three_vertices__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T20:01:45.624351+00:00
-- url     : https://prove2.me/theorems/293787da-4b73-4bb8-b4f9-49ac7bd93d8f
-- title:
--   Strict planar extension with at least three vertices
-- statement:
--   A disconnected graph with at least three vertices and a supplied crossing-free drawing has a strict planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension_of_three_vertices__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G < H ∧ HasPlanarDrawingOn H := by sorry
