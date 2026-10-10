-- Prove2me | Theorems.Thm_PriceQualityService_Oligopoly_aggregate_ge_monopoly_root
-- name    : PriceQualityService.Oligopoly.aggregate_ge_monopoly_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:56.12845+00:00
-- url     : https://prove2.me/theorems/73a164a7-e587-4c20-bb84-1eddae59e5b1
-- title:
--   The equilibrium aggregate $A^o$ is at least the monopoly root $m^*$
-- statement:
--   Fix quality levels $\mathbf q$ and durations $\mathbf t$. Then:
--
--   1. the equation
--   $$
--   m = 1 + \sum_{i \in \mathcal N} \exp\big(\alpha_i q_i - c_i q_i^2 - t_i(a_i - b_i q_i - s_i) - m\big)
--   $$
--   has exactly one real solution $m^*$;
--   2. every positive root $A^o$ of the aggregate equation $\frac1A + \sum_j \exp(\alpha_j q_j - \varphi_j(A) + t_j s_j)/A = 1$ satisfies $A^o \ge m^*$.
--
--   At the monopoly qualities and durations, $m^* = 1 + r^*$ is the monopolist's common markup (Theorem 1), so this compares the competitive aggregate $A^o$ with the monopolist's.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 3 (PDF p. 36), proof of Theorem 2

import Mathlib
import Definitions.Def_PriceQualityService_Oligopoly_PriceRoot

namespace PriceQualityService.Oligopoly

/-- Online Supplement p. 3: the equation
`m = 1 + ∑_i exp(α_i q_i − c_i q_i² − t_i(a_i − b_i q_i − s_i) − m)` has exactly one solution
`m*`, and every positive root `A^o` of the aggregate equation satisfies `A^o ≥ m*`. -/
theorem aggregate_ge_monopoly_root {N : ℕ} (α a b c s q t : Fin N → ℝ) :
    (∃! m : ℝ, m = 1 + ∑ i, Real.exp (α i * q i - c i * q i ^ 2 - t i * (a i - b i * q i - s i) - m)) ∧
      ∀ A m : ℝ, 0 < A → IsAggregateRoot α a b c s q t A →
        m = 1 + ∑ i, Real.exp (α i * q i - c i * q i ^ 2 - t i * (a i - b i * q i - s i) - m) →
        m ≤ A := by sorry

end PriceQualityService.Oligopoly
