-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_supergraph_of_component_step
-- name    : WilliamsonShmoys.connected_supergraph_of_component_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:37:16.276416+00:00
-- url     : https://prove2.me/theorems/b1c6d2a3-5960-4006-a91b-1cf575e39dba
-- title:
--   Iterating strict component-reducing extensions
-- statement:
--   If every disconnected graph satisfying a property has a property-preserving supergraph with strictly fewer connected components, then every graph satisfying that property has a connected supergraph satisfying it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.connected_supergraph_of_component_step
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hcomp : ∀ G : SimpleGraph V, Nonempty (Fintype G.ConnectedComponent))
    (hstep : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∀ (iG : Fintype G.ConnectedComponent),
        ∃ (H : SimpleGraph V), ∃ (iH : Fintype H.ConnectedComponent),
          G ≤ H ∧ P H ∧
            @Fintype.card H.ConnectedComponent iH <
              @Fintype.card G.ConnectedComponent iG) :
    ∀ G : SimpleGraph V, P G →
      ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ P H := by sorry
