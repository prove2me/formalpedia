-- Prove2me | Theorems.Thm_WilliamsonShmoys_card_sum_of_partition
-- name    : WilliamsonShmoys.card_sum_of_partition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:31:29.830205+00:00
-- url     : https://prove2.me/theorems/01d13fe9-c730-41f0-ae43-cba0a28ecc74
-- title:
--   Sum block cardinalities over a finite partition
-- statement:
--   The sum of the sizes of pairwise disjoint blocks covering the finite vertex type equals its cardinality. This follows by counting the pairs consisting of a block and one of its vertices, using coverage and disjointness to identify each vertex with exactly one such pair.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.card_sum_of_partition
    {V : Type} [Fintype V] [DecidableEq V]
    (C : Finset (Finset V))
    (hcover : ∀ v : V, ∃ S, S ∈ C ∧ v ∈ S)
    (hdisjoint : ∀ S, S ∈ C → ∀ T, T ∈ C → S ≠ T → Disjoint S T) :
    (∑ S ∈ C, S.card) = Fintype.card V := by sorry
