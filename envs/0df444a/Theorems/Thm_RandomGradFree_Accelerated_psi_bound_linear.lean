-- Prove2me | Theorems.Thm_RandomGradFree_Accelerated_psi_bound_linear
-- name    : RandomGradFree.Accelerated.psi_bound_linear
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T09:41:42.695977+00:00
-- url     : https://prove2.me/theorems/9dc96f11-70cf-4e01-959f-d7679701c4a8
-- title:
--   The convergence factor psi_k of the accelerated random method decays geometrically (Nesterov-Spokoiny Theorem 9, Eq. (62)(b))
-- statement:
--   Let (alpha_j) be a real sequence with 0 <= alpha_j <= 1 for every j, let n be a natural number, and let kappa be a real number with 0 <= kappa <= 1. Let psi be the convergence-factor sequence of the accelerated random method of Nesterov-Spokoiny (paper p. 550: psi_k = prod_{i<k}(1 - alpha_i)). If alpha_j >= sqrt(kappa)/(4*(n+4)) for every j, then psi alpha k <= (1 - sqrt(kappa)/(4*(n+4)))^k for every k. This is conjunct (b) of Theorem 9 (Eq. (62)): with c = sqrt(kappa)/(4*(n+4)) <= 1, each factor 1 - alpha_j satisfies 0 <= 1 - alpha_j <= 1 - c, so the k-fold product is at most (1 - c)^k.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 550, Theorem 9, Eq. (62)(b)

import Mathlib
import Definitions.Def_RandomGradFree_Accelerated_psi

namespace RandomGradFree.Accelerated

theorem psi_bound_linear (α : ℕ → ℝ) (n : ℕ) (κ : ℝ)
    (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hακ : ∀ j, Real.sqrt κ / (4 * ((n : ℝ) + 4)) ≤ α j)
    (k : ℕ) :
    psi α k ≤ (1 - Real.sqrt κ / (4 * ((n : ℝ) + 4))) ^ k := by
  sorry

end RandomGradFree.Accelerated
