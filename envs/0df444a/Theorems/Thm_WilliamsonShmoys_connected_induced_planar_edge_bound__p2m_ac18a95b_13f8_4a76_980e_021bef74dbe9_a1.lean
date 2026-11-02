-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_induced_planar_edge_bound__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
-- name    : WilliamsonShmoys.connected_induced_planar_edge_bound__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:34:45.3712+00:00
-- url     : https://prove2.me/theorems/ed6487b5-3fd2-47fb-a969-c3848ac24208
-- title:
--   Connected induced planar edge bound
-- statement:
--   For a graph with the specified crossing-free drawing, every connected induced subgraph on at least three vertices satisfies the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.connected_induced_planar_edge_bound__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∀ s : Finset V, 3 <= s.card →
      (N.induce (s : Set V)).Connected →
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6 := by sorry
