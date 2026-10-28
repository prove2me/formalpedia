-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_nonadjacent_pair
-- name    : WilliamsonShmoys.disconnected_has_nonadjacent_pair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:09:14.333471+00:00
-- url     : https://prove2.me/theorems/9cab1508-a722-469e-84c8-76b3750b8e11
-- title:
--   A nonempty disconnected graph has a missing edge
-- statement:
--   A finite graph on at least three vertices that is disconnected has two distinct nonadjacent vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_has_nonadjacent_pair
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdisc : ¬ Q.Connected) :
    ∃ u v, u ≠ v ∧ ¬ Q.Adj u v := by sorry
