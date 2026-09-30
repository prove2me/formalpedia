-- Prove2me | Theorems.Thm_RandomGradFree_Accelerated_psi_bound_quadratic
-- name    : RandomGradFree.Accelerated.psi_bound_quadratic
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T09:41:50.362925+00:00
-- url     : https://prove2.me/theorems/0515235f-171b-4f6a-b134-a469a89c40fa
-- title:
--   The product sequence psi_k of the accelerated random method decays quadratically (Nesterov-Spokoiny Theorem 9, Eq. (62)(c))
-- statement:
--   Let n be a natural number and (alpha_k) a real sequence with 0 <= alpha_j <= 1 for every j. Let (gamma_k) be a real sequence, L_1 > 0 a real number, and suppose alpha_j >= sqrt(gamma_0 / L_1) / (4 * (n + 4)) for every j (the step-size lower bound used in the paper's proof of Eq. (62)(c), from the alpha-recurrence with theta_n = 1/(16*(n+4)^2*L_1) and gamma nondecreasing). Let psi be the product sequence of the accelerated random method of Nesterov-Spokoiny (paper p. 550: psi_k = prod_{i=0}^{k-1} (1 - alpha_i)). Then psi alpha k <= 1 / (1 + k / (8 * (n + 4)) * sqrt(gamma_0 / L_1))^2 for every k. This is conjunct (c) of Theorem 9 (Eq. (62)): since 1/sqrt(psi_{k+1}) - 1/sqrt(psi_k) >= alpha_k/2, the values 1/sqrt(psi_k) grow at least linearly in k, giving the O(n^2/k^2) accelerated rate of a method that uses only function values. It is a PROVE target in the RandomGradFree.Accelerated conjunct family.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 550, Theorem 9, Eq. (62)(c)

import Mathlib
import Definitions.Def_RandomGradFree_Accelerated_psi

namespace RandomGradFree.Accelerated

theorem psi_bound_quadratic (n : ℕ) (α : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1)
    (γ : ℕ → ℝ) (L₁ : ℝ) (hL₁ : 0 < L₁)
    (hαlow : ∀ j, Real.sqrt (γ 0 / L₁) / (4 * ((n : ℝ) + 4)) ≤ α j)
    (k : ℕ) :
    psi α k ≤ 1 / (1 + k / (8 * ((n : ℝ) + 4)) * Real.sqrt (γ 0 / L₁)) ^ 2 := by
  sorry

end RandomGradFree.Accelerated
