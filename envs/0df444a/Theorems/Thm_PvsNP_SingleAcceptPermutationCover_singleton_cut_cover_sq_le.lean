-- Prove2me | Theorems.Thm_PvsNP_SingleAcceptPermutationCover_singleton_cut_cover_sq_le
-- name    : PvsNP.SingleAcceptPermutationCover.singleton_cut_cover_sq_le
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T05:30:19.824604+00:00
-- url     : https://prove2.me/theorems/bafdec7a-3de2-4fb2-a6da-4589067d93ff
-- title:
--   A single accepting state bounds disjointness coverage across a permutation cut
-- statement:
--   For each prefix string of r bits, let a map give a state in a finite state space. For each suffix string of r bits, let a permutation of that state space give the suffix computation. Fix one accepting state. Assume every pair whose prefix state maps to the accepting state under its suffix permutation has no coordinate at which both strings have a 1. Then the square of the number of accepted ordered pairs is at most 8^r.
-- source:
--   Finite rectangle and Cauchy–Schwarz argument for the singleton accepting state model considered by Chen, Lyu, Tal and Wu, ICALP 2023, https://doi.org/10.4230/LIPIcs.ICALP.2023.39. This theorem concerns the cut that separates the two input strings.

import Mathlib

theorem PvsNP.SingleAcceptPermutationCover.singleton_cut_cover_sq_le {r : ℕ} {Q : Type*} [Fintype Q]
    (startState : (Fin r → Bool) → Q)
    (suffix : (Fin r → Bool) → Equiv.Perm Q) (accept : Q)
    (safe : ∀ x y, suffix y (startState x) = accept →
      ∀ i, ¬ (x i = true ∧ y i = true)) :
    (Nat.card {p : (Fin r → Bool) × (Fin r → Bool) //
      suffix p.2 (startState p.1) = accept}) ^ 2 ≤ 8 ^ r := by sorry
