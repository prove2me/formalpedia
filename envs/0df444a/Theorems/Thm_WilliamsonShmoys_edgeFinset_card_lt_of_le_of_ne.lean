-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_lt_of_le_of_ne
-- name    : WilliamsonShmoys.edgeFinset_card_lt_of_le_of_ne
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:04:20.146451+00:00
-- url     : https://prove2.me/theorems/ad651318-9b5f-42b0-b0b3-436b26600c95
-- title:
--   Strict edge-count growth under proper graph inclusion
-- statement:
--   For finite graphs on the same vertex type, proper graph inclusion strictly increases the edge count, given finite edge-set instances.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeFinset_card_lt_of_le_of_ne
    {V : Type} [Fintype V]
    {G H : SimpleGraph V}
    (hGFinite : Fintype G.edgeSet)
    (hHFinite : Fintype H.edgeSet)
    (hGH : G ≤ H)
    (hne : H ≠ G) :
    G.edgeFinset.card < H.edgeFinset.card := by sorry
