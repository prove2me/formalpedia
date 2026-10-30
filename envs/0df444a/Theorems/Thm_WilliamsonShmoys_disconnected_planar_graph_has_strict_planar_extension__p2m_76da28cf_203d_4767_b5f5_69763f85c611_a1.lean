-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_strict_planar_extension__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1
-- name    : WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T18:45:34.547326+00:00
-- url     : https://prove2.me/theorems/70e8c091-7bdb-4671-99d7-abbf72db95dd
-- title:
--   Strict planar extension of a disconnected plane graph
-- statement:
--   Every disconnected finite graph with the supplied plane drawing has a strict planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G < H ∧ HasPlanarDrawingOn H := by sorry
