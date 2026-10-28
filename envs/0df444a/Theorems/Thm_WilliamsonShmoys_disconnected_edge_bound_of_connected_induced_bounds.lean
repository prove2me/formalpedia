-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_edge_bound_of_connected_induced_bounds
-- name    : WilliamsonShmoys.disconnected_edge_bound_of_connected_induced_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:19:17.051085+00:00
-- url     : https://prove2.me/theorems/3c45a08c-18ee-404f-9b47-ba446a71aeb0
-- title:
--   Aggregate connected induced-subgraph bounds
-- statement:
--   If a finite disconnected graph with at least three vertices has the 3|S|−6 edge bound on every connected induced subset of size at least three, then the whole graph satisfies the same bound. The proof sums the bounds over connected components and handles components of size one or two directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_edge_bound_of_connected_induced_bounds
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hdisc : ¬ K.Connected)
    (hlocal : ∀ (S : Set V) [Fintype S], 3 <= Fintype.card S →
      (K.induce S).Connected →
      (K.induce S).edgeSet.ncard + 6 <= 3 * Fintype.card S) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
