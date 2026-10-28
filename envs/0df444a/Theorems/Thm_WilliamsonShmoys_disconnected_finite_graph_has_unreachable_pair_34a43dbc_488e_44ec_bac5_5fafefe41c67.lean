-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_finite_graph_has_unreachable_pair_34a43dbc_488e_44ec_bac5_5fafefe41c67
-- name    : WilliamsonShmoys.disconnected_finite_graph_has_unreachable_pair_34a43dbc_488e_44ec_bac5_5fafefe41c67
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:09:02.690062+00:00
-- url     : https://prove2.me/theorems/03b04c4f-f956-4aa8-947d-df6499ef13dc
-- title:
--   A disconnected finite graph has an unreachable vertex pair
-- statement:
--   A disconnected graph on a finite nonempty vertex type has two vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_finite_graph_has_unreachable_pair_34a43dbc_488e_44ec_bac5_5fafefe41c67
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ u v : V, ¬ K.Reachable u v := by sorry
