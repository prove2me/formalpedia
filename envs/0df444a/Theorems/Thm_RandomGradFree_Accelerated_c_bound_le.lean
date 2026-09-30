-- Prove2me | Theorems.Thm_RandomGradFree_Accelerated_c_bound_le
-- name    : RandomGradFree.Accelerated.c_bound_le
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T08:37:16.274391+00:00
-- url     : https://prove2.me/theorems/dbb2f805-4cb4-4192-9196-bb14abacf7f1
-- title:
--   The accumulation sequence C_k of the accelerated random method is at most k (Nesterov-Spokoiny Theorem 9, Eq. (62)(d))
-- statement:
--   Let (alpha_k) be a real sequence with 0 <= alpha_j <= 1 for every j, and let C be the accumulation sequence of the accelerated random method of Nesterov-Spokoiny (paper p. 550: C_0 = 0, C_k = 1 + sum_{i=1}^{k-1} prod_{j=k-i}^{k-1} (1 - alpha_j)). Then C alpha k <= k for every k. This is conjunct (d) of Theorem 9 (Eq. (62)), the easiest of the four pure-sequence conjuncts: since 0 <= 1 - alpha_j <= 1, each product in the sum is at most 1, and there are k - 1 summands, so C_k <= 1 + (k - 1) = k (and C_0 = 0 <= 0). It is the natural first PROVE target in the RandomGradFree.Accelerated conjunct family.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 550, Theorem 9, Eq. (62)(d)

import Mathlib
import Definitions.Def_RandomGradFree_Accelerated_C

namespace RandomGradFree.Accelerated

theorem c_bound_le (α : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1) (k : ℕ) :
    C α k ≤ (k : ℝ) := by
  sorry

end RandomGradFree.Accelerated
