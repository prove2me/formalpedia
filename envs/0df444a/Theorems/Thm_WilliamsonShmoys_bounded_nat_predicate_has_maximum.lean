-- Prove2me | Theorems.Thm_WilliamsonShmoys_bounded_nat_predicate_has_maximum
-- name    : WilliamsonShmoys.bounded_nat_predicate_has_maximum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:35:22.328762+00:00
-- url     : https://prove2.me/theorems/323789d0-1f8b-40cb-86a5-b50444d8daa0
-- title:
--   A nonempty bounded family of natural numbers has a maximum
-- statement:
--   For any predicate on natural numbers, if some value satisfies it and all satisfying values are at most a fixed bound, then one satisfying value is at least every other satisfying value.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.bounded_nat_predicate_has_maximum (P : Nat → Prop) (hP : ∃ n, P n) (B : Nat) (hB : ∀ n, P n → n ≤ B) : ∃ m, P m ∧ ∀ n, P n → n ≤ m := by sorry
