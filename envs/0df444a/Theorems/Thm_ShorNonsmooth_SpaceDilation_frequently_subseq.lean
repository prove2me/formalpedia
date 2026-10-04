-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_frequently_subseq
-- name    : ShorNonsmooth.SpaceDilation.frequently_subseq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:11:20.471886+00:00
-- url     : https://prove2.me/theorems/947ab96b-2d23-453a-9a29-948b78e7bdb3
-- title:
--   An infinitely-often predicate holds along a strictly increasing subsequence
-- statement:
--   If a predicate $Q$ on natural numbers holds at arbitrarily large indices (for every $J$ there is $j \ge J$ with $Q(j)$), then there is a strictly increasing sequence $k_0 < k_1 < \cdots$ with $Q(k_p)$ for all $p$.
-- source:
--   Standard infinitely-often to subsequence extraction, isolating the index-construction step in the proof of Theorem 3.1 of Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 53.

import Mathlib

namespace ShorNonsmooth.SpaceDilation

/-- If a predicate holds at arbitrarily large indices, it holds along a strictly increasing index sequence. Used in Theorem 3.1 to pass from `for every J there is j ≥ J with ‖g̃_j‖ < c P_j^{-1/n}` to the subsequence `k_p`. -/
theorem frequently_subseq (Q : ℕ → Prop)
    (h : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ Q j) :
    ∃ kp : ℕ → ℕ, StrictMono kp ∧ ∀ p : ℕ, Q (kp p) := by sorry

end ShorNonsmooth.SpaceDilation
