-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_of_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1
-- name    : WilliamsonShmoys.connected_of_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:51:50.366471+00:00
-- url     : https://prove2.me/theorems/306c594f-78c4-4ee3-bc15-372f1c5fe32d
-- title:
--   A maximal invariant extension is connected
-- statement:
--   Under the local edge-extension hypothesis, a P-satisfying graph maximal among P-satisfying extensions must be connected. If it were disconnected, the hypothesis would supply a P-extension with an edge joining previously unreachable vertices; maximality forces that extension to equal the original graph, making the edge a path and contradicting non-reachability.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.connected_of_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (step : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ K.Adj u v)
    (H : SimpleGraph V) (hH : P H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → P K → K = H) :
    H.Connected := by sorry
