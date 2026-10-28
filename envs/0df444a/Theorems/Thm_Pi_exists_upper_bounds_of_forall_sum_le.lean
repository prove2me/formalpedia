-- Prove2me | Theorems.Thm_Pi_exists_upper_bounds_of_forall_sum_le
-- name    : Pi.exists_upper_bounds_of_forall_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T07:51:30.148951+00:00
-- url     : https://prove2.me/theorems/256f9285-4d6a-470f-9438-3f67b85fd217
-- title:
--   A bound on every selection sum is witnessed by componentwise upper bounds
-- statement:
--   Let $N \ge 1$, let $T_0, \dots, T_{N-1}$ be nonempty sets of real numbers, and let
--   $B \in \mathbb{R}$ bound every selection sum:
--
--   $$
--   \sum_{i} r_i \le B \qquad \text{whenever } r_i \in T_i \text{ for every } i .
--   $$
--
--   Then the bound is already witnessed by a single rectangular box: there are
--   $s_0, \dots, s_{N-1} \in \mathbb{R}$ with
--
--   $$
--   r \le s_i \ \text{ for every } r \in T_i \text{ and every } i, \qquad \sum_{i} s_i \le B .
--   $$
--
--   The hypothesis couples the indices -- it is a bound on sums -- and the conclusion decouples
--   them, which is what makes the statement useful: an estimate quantified over a product of sets
--   becomes finitely many independent estimates. Each $s_i$ is necessarily an upper bound for
--   $T_i$, so the sets are automatically bounded above even though nothing said so. This is the
--   rectangularization step behind separable reformulations of jointly constrained problems.
-- source:
--   P. Mohajerin Esfahani and D. Kuhn, Data-driven distributionally robust optimization using the Wasserstein metric: performance guarantees and tractable reformulations, Mathematical Programming 171 (2018), 115-166. Carved from https://prove2.me/submissions/9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 709-763, the accepted proof of WassDDRO.Extremal.theorem_4_4. The same statement is proved inline in https://prove2.me/submissions/6e4986f7-2b7e-4a8d-97e1-f19f9c2537ac as well, the accepted proof of WassDDRO.Reduction.theorem_4_2, so two missions were each carrying their own derivation of it

import Mathlib

set_option autoImplicit false
open Filter Topology Set

theorem Pi.exists_upper_bounds_of_forall_sum_le {N : ℕ} (hN : 0 < N)
    (T : Fin N → Set ℝ) (hne : ∀ i, (T i).Nonempty) (B : ℝ)
    (hbound : ∀ r : Fin N → ℝ, (∀ i, r i∈T i) → (∑ i, r i) ≤ B) :
    ∃ s : Fin N → ℝ, (∀ i r, r∈T i → r ≤ s i) ∧ (∑ i, s i) ≤ B := by sorry
