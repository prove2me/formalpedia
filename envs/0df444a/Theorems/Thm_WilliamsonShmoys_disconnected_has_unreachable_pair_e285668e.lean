-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_unreachable_pair_e285668e
-- name    : WilliamsonShmoys.disconnected_has_unreachable_pair_e285668e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:01:44.389478+00:00
-- url     : https://prove2.me/theorems/40cee811-dc1d-4a23-9c61-f4a7f54c7ef3
-- title:
--   Disconnectedness provides distinct unreachable vertices
-- statement:
--   In a finite graph with at least three vertices, disconnectedness yields distinct vertices that are not connected by a path. The cardinality hypothesis is retained from the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_has_unreachable_pair_e285668e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDisconnected : ¬ L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ u v : V, u ≠ v ∧ ¬ L.Reachable u v := by sorry
