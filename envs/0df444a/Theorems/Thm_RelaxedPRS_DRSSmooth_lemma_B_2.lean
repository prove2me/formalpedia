-- Prove2me | Theorems.Thm_RelaxedPRS_DRSSmooth_lemma_B_2
-- name    : RelaxedPRS.DRSSmooth.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:59.596989+00:00
-- url     : https://prove2.me/theorems/649d9573-6bff-40f6-a86f-c1c5c62c91bc
-- title:
--   Lemma B.2, p. 34 — largest admissible stepsize ratio
-- statement:
--   For $\beta>0$, consider pairs $\gamma>0$, $\theta\in[0,1]$ satisfying $\theta\gamma^2\le2\gamma\beta-\gamma^3/\beta$ and $(1-\theta)\gamma^2/\beta^2\le1$. The least upper bound of their ratios $\gamma/\beta$ is the positive root $\kappa$ of $\kappa^3+\kappa^2-2\kappa-1=0$:
--   $$\kappa=\sup\left\{\frac{\gamma}{\beta}:\gamma,\theta\text{ satisfy the two constraints}\right\}.$$
--   The pair $(\gamma^*,\theta^*)=(\kappa\beta,1-1/\kappa^2)$ satisfies both constraints with equality. This determines the stepsize threshold used in the nonergodic result.
--
--   **Formalization Note** The supremum is expressed as a least-upper-bound predicate, which preserves its meaning for real numbers.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 34, Lemma B.2 (B.8), Remark B.1

import Mathlib
import Definitions.Def_RelaxedPRS_DRSSmooth_Setting

open InnerProductSpace Filter

namespace RelaxedPRS.DRSSmooth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Lemma B.2, p. 34, (B.8), and the optimizer following it. -/
theorem lemma_B_2 (β : ℝ) (hβ : 0 < β) (κ : ℝ)
    (hκ : 0 < κ ∧ κ ^ 3 + κ ^ 2 - 2 * κ - 1 = 0) :
    IsLUB {r : ℝ | ∃ γ θ : ℝ, 0 < γ ∧ 0 ≤ θ ∧ θ ≤ 1 ∧
      θ * γ ^ 2 ≤ 2 * γ * β - γ ^ 3 / β ∧
      (1 - θ) * γ ^ 2 / β ^ 2 ≤ 1 ∧ r = γ / β} κ ∧
    (0 ≤ 1 - 1 / κ ^ 2 ∧ 1 - 1 / κ ^ 2 ≤ 1 ∧
      (1 - 1 / κ ^ 2) * (κ * β) ^ 2 = 2 * (κ * β) * β - (κ * β) ^ 3 / β ∧
      (1 - (1 - 1 / κ ^ 2)) * (κ * β) ^ 2 / β ^ 2 = 1) := by sorry

end RelaxedPRS.DRSSmooth
