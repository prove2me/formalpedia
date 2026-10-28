-- Prove2me | Theorems.Thm_WilliamsonShmoys_aggregate_piece_edge_bounds
-- name    : WilliamsonShmoys.aggregate_piece_edge_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:52:19.215993+00:00
-- url     : https://prove2.me/theorems/1cdcd9bc-6fb2-4cc4-bfd9-2b326e78b129
-- title:
--   Aggregate local edge margins over nonempty blocks
-- statement:
--   Local bounds with a three-unit margin on every nonempty small block and a six-unit margin on every large block imply the aggregate six-unit margin when the total block size is at least three. If a large block exists, it supplies the extra margin beyond the three units contributed by each block. Otherwise all blocks are nonempty and small, so total size at least three implies at least two blocks. A finite-sum argument with these two cases proves the conclusion; this isolates the arithmetic from graph edge bookkeeping.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.aggregate_piece_edge_bounds
    {V : Type} [Fintype V] [DecidableEq V]
    (C : Finset (Finset V)) (e : Finset V → Nat)
    (hV : 3 ≤ Fintype.card V)
    (hcard : (∑ S ∈ C, S.card) = Fintype.card V)
    (hne : ∀ S, S ∈ C → 0 < S.card)
    (hsmall : ∀ S, S ∈ C → 0 < S.card → S.card < 3 → e S + 3 ≤ 3 * S.card)
    (hlarge : ∀ S, S ∈ C → 3 ≤ S.card → e S + 6 ≤ 3 * S.card) :
    (∑ S ∈ C, e S) + 6 ≤ 3 * (∑ S ∈ C, S.card) := by sorry
