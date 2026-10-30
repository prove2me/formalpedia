-- Prove2me | Theorems.Thm_SubscriptionPlanning_GrandOptimal_theorem_2_sufficiency
-- name    : SubscriptionPlanning.GrandOptimal.theorem_2_sufficiency
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:10.561986+00:00
-- url     : https://prove2.me/theorems/4796871e-4044-4e16-b508-31ca5f8da832
-- title:
--   Theorem 2 (first bullet), p. 13 (PDF 14) — under Condition 2, for any q and λ some fee for the grand set alone achieves the optimal revenue
-- statement:
--   Fix rental prices $\mathbf r \ge 0$ satisfying Condition 2. Then for any masses $\mathbf q$ and usage rates $\boldsymbol\lambda$ of the user types there is a fee $P$ for the grand set $\mathcal M$, together with subscription decisions $\sigma_i$ consistent with each type's incentives ($\sigma_i$ true only if $P \le \lambda_i T\,\mathrm{SubGain}(i,\mathcal M,\mathbf r)$, false only if $P \ge \lambda_i T\,\mathrm{SubGain}(i,\mathcal M,\mathbf r)$), whose revenue is at least the revenue of every feasible subscription planning:
--   $$\sum_i q_i\big(p(S_i) + \lambda_i T\,\mathrm{Rent}(i,S_i,\mathbf r)\big) \le \sum_{i:\,\sigma_i} q_i\big(P + \lambda_i T\,\mathrm{Rent}(i,\mathcal M,\mathbf r)\big) + \sum_{i:\,\neg\sigma_i} q_i\,\lambda_i T\,\mathrm{Rent}(i,\emptyset,\mathbf r)$$
--   for every fee function $p$ with $p(\emptyset) = 0$ and every assignment $S_1, \dots, S_n$ satisfying the incentive constraints (3).
--
--   Under Condition 2, offering a single all-inclusive subscription alongside the rental prices loses nothing against any menu of subscription sets. The grand subscription is itself a feasible planning (price every other set prohibitively), so its revenue is the optimal revenue.
--
--   **Formalization Note** "Achieves the optimal revenue" is stated as domination of every feasible planning, with no supremum. The model may be any probability space with integrable values of any joint law; the masses, usage rates and horizon are arbitrary subject to $q_i \ge 0$, $\sum_i q_i = 1$, $\lambda_i > 0$, $T > 0$. The hypothesis $\mathbf r \ge 0$ and the convention $p(\emptyset) = 0$ are added. Only the first bullet of Theorem 2 is posed.
-- source:
--   Alaei, Makhdoumi, Malekian, Optimal Subscription Planning for Digital Goods, working paper (SSRN 3476296; Operations Research, doi:10.1287/opre.2023.2468), p. 13, Theorem 2, first bullet (proof pp. 33–34)

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting

namespace SubscriptionPlanning.GrandOptimal
theorem theorem_2_sufficiency {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model n m Ω)
    (hM : M.Valid) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (hC : Condition2 M r) :
    ∃ (P : ℝ) (σ : Fin n → Bool), IsGrandFeasible M r P σ ∧
      ∀ (p : Finset (Fin m) → ℝ) (S : Fin n → Finset (Fin m)),
        IsFeasible M r p S → revenue M r p S ≤ grandRevenue M r P σ := by sorry
end SubscriptionPlanning.GrandOptimal
