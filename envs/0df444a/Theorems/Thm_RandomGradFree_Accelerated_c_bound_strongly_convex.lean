-- Prove2me | Theorems.Thm_RandomGradFree_Accelerated_c_bound_strongly_convex
-- name    : RandomGradFree.Accelerated.c_bound_strongly_convex
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T10:37:12.402212+00:00
-- url     : https://prove2.me/theorems/b5b825f4-4c5b-44aa-bcdb-8332c4137209
-- title:
--   The accumulation sequence C_k of the accelerated random method is bounded in the strongly-convex regime (Nesterov-Spokoiny Theorem 9, Eq. (62)(e))
-- statement:
--   Let (alpha_j) be a real sequence with 0 <= alpha_j <= 1 for every j, let n be the ambient dimension, and let tau > 0 and L_1 > 0 be the strong-convexity and smoothness parameters of the Nesterov-Spokoiny accelerated random method. Suppose alpha_j >= sqrt(tau / L_1) / (4 * (n + 4)) for every j (the recurrence floor of the step sizes in the strongly-convex regime). Let C be the accumulation sequence (paper p. 550: C_0 = 0, C_k = 1 + sum_{i=1}^{k-1} prod_{j=k-i}^{k-1} (1 - alpha_j)). Then C alpha k <= 4 * (n + 4) / sqrt(tau / L_1) for every k. This is conjunct (e) of Theorem 9 (Eq. (62)): in the strongly-convex regime each inner product is bounded by a geometric term (1 - sqrt(kappa)/(4*(n+4)))^i with kappa = tau/L_1, so the series sums to 4*(n+4)/sqrt(kappa).
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 550, Theorem 9, Eq. (62)(e)

import Mathlib
import Definitions.Def_RandomGradFree_Accelerated_C

namespace RandomGradFree.Accelerated

theorem c_bound_strongly_convex (n : ℕ) (α : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1)
    (τ : ℝ) (hτ : 0 < τ) (L₁ : ℝ) (hL₁ : 0 < L₁)
    (hακ : ∀ j, Real.sqrt (τ / L₁) / (4 * ((n : ℝ) + 4)) ≤ α j)
    (k : ℕ) :
    C α k ≤ 4 * ((n : ℝ) + 4) / Real.sqrt (τ / L₁) := by
  sorry

end RandomGradFree.Accelerated
