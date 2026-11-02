-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_supergraph_from_one_edge_augmentations__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
-- name    : WilliamsonShmoys.connected_supergraph_from_one_edge_augmentations__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:59:15.34563+00:00
-- url     : https://prove2.me/theorems/cd1fec5c-6619-45ff-8b92-8d3bff9da8a8
-- title:
--   Finite accumulation of one-edge augmentations connects a graph
-- statement:
--   For a finite vertex type, suppose a property is preserved by a step that adds exactly one absent edge between unreachable vertices, and such a step is always available whenever a graph with the property is disconnected. Then every graph with the property has a connected supergraph with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_supergraph_from_one_edge_augmentations__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hstep : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ a b : V, ∃ H : SimpleGraph V,
        ¬ G.Adj a b ∧ ¬ G.Reachable a b ∧
        (∀ u v, H.Adj u v ↔
          G.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a)) ∧
        P H)
    (K : SimpleGraph V)
    (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ P H := by sorry
