-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_extension_of_pairwise_bridge_closure__p2m_596e37ff_bf61_48b7_90c3_a4814329de9c_a1
-- name    : WilliamsonShmoys.connected_extension_of_pairwise_bridge_closure__p2m_596e37ff_bf61_48b7_90c3_a4814329de9c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:03:28.562895+00:00
-- url     : https://prove2.me/theorems/51934198-d634-4c07-af8d-bda44ea7fae9
-- title:
--   Connected extension from pairwise bridge closure
-- statement:
--   If a property of finite graphs is preserved whenever an edge is added between unreachable vertices, then every graph with that property has a connected supergraph with the same property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_extension_of_pairwise_bridge_closure__p2m_596e37ff_bf61_48b7_90c3_a4814329de9c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : P K)
    (hstep : ∀ (G : SimpleGraph V), (dG : DecidableRel G.Adj) →
      P G →
      ∀ u v, ¬ G.Reachable u v →
        ∃ H : SimpleGraph V,
          (∀ a b, H.Adj a b ↔
            G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
          P H) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ P H := by
  sorry
