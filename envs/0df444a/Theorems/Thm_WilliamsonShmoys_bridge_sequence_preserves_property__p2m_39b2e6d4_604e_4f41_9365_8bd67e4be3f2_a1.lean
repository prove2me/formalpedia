-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridge_sequence_preserves_property__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
-- name    : WilliamsonShmoys.bridge_sequence_preserves_property__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:48:34.434948+00:00
-- url     : https://prove2.me/theorems/2137e45a-ddbe-4a4f-9b12-b3654d5e6afd
-- title:
--   Bridge-step closure preserves a property along a sequence
-- statement:
--   If P holds initially and every unreachable pair admits an exact single-edge extension preserving P, then P holds at the end of any sequence whose steps add such edges. The initial equality identifies the sequence's first graph with M. Induction over the steps applies hbridge and uses the adjacency characterization to identify each supplied extension with the next sequence graph; the same induction composes the supergraph relation. This removes predicate propagation and edge-inclusion bookkeeping from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.bridge_sequence_preserves_property__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P M)
    (hbridge : ∀ (G : SimpleGraph V), P G →
      ∀ x y : V, ¬ G.Reachable x y →
        ∃ N : SimpleGraph V,
          G ≤ N ∧
          (∀ u v, N.Adj u v ↔
            G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) ∧
          P N)
    (n : Nat)
    (f : Fin (n + 1) → SimpleGraph V)
    (hstart : f 0 = M)
    (hstep : ∀ i : Fin n, ∃ x y : V,
      ¬ (f i.castSucc).Reachable x y ∧
      ∀ u v : V,
        (f i.succ).Adj u v ↔
          (f i.castSucc).Adj u v ∨
            ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) :
    M ≤ f (Fin.last n) ∧ P (f (Fin.last n)) := by
  sorry
