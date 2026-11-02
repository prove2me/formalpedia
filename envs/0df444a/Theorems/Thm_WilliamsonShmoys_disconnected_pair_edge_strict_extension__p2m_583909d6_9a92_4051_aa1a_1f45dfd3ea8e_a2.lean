-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_pair_edge_strict_extension__p2m_583909d6_9a92_4051_aa1a_1f45dfd3ea8e_a2
-- name    : WilliamsonShmoys.disconnected_pair_edge_strict_extension__p2m_583909d6_9a92_4051_aa1a_1f45dfd3ea8e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:16:15.258746+00:00
-- url     : https://prove2.me/theorems/55a5c6d6-7e43-4543-abd7-63ebfe071947
-- title:
--   A disconnected graph has a strict edge extension from an unreachable pair
-- statement:
--   For a finite ordered graph with at least three vertices that is disconnected, select vertices in different components. They are unreachable from one another, and adjoining the edge between them produces a strict supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_pair_edge_strict_extension__p2m_583909d6_9a92_4051_aa1a_1f45dfd3ea8e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDisconnected : ¬ H.Connected)
    (hn : Nat.le 3 (Fintype.card V)) :
    ∃ u v : V,
      ¬ H.Reachable u v ∧
      H ≤ H ⊔ SimpleGraph.edge u v ∧
      H ≠ H ⊔ SimpleGraph.edge u v := by
  sorry
