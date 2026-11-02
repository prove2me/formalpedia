-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_planar_strict_extension__p2m_a0a9770d_b636_48de_8b32_1b32b62691e8_a1
-- name    : WilliamsonShmoys.disconnected_planar_graph_has_planar_strict_extension__p2m_a0a9770d_b636_48de_8b32_1b32b62691e8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:00:42.465224+00:00
-- url     : https://prove2.me/theorems/b7a1cfc0-b36e-4034-a5fa-2e691bcea0a4
-- title:
--   A disconnected planar drawing admits a proper planar supergraph
-- statement:
--   Every disconnected finite graph with a crossing-free drawing on its ordered vertex type has a planar supergraph on the same vertices that adds at least one edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_graph_has_planar_strict_extension__p2m_a0a9770d_b636_48de_8b32_1b32b62691e8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hdisc : ¬ K.Connected) :
    ∃ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      HasPlanarDrawingOn L ∧
      ∃ u v, L.Adj u v ∧ ¬ K.Adj u v := by sorry
