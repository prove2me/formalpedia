-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_nonempty_has_unreachable_pair
-- name    : WilliamsonShmoys.disconnected_nonempty_has_unreachable_pair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:28:34.055049+00:00
-- url     : https://prove2.me/theorems/1068d8ca-b2e2-4bd2-9321-888c0747bfcb
-- title:
--   A nonempty disconnected graph has an unreachable pair
-- statement:
--   A finite nonempty graph that is not connected has two vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_nonempty_has_unreachable_pair
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (hV : 0 < Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ u v : V, ¬ H.Reachable u v := by sorry
