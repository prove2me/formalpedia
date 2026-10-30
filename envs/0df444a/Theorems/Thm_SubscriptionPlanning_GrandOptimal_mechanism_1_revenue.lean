-- Prove2me | Theorems.Thm_SubscriptionPlanning_GrandOptimal_mechanism_1_revenue
-- name    : SubscriptionPlanning.GrandOptimal.mechanism_1_revenue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:26.591988+00:00
-- url     : https://prove2.me/theorems/9b1b29e1-6c83-4a9f-89ea-a2aee5a48a0b
-- title:
--   Mechanism 1, p. 14 (PDF 15), as an inequality for every feasible planning — the grand-fee lottery earns at least the planning's revenue
-- statement:
--   Fix rental prices $\mathbf r \ge 0$ satisfying Condition 2 and a feasible subscription planning $(p, S_1, \dots, S_n)$ (incentive constraints (3), $p(\emptyset) = 0$). Write $A_k = \lambda_k T\,\mathrm{SubGain}(k,\mathcal M,\mathbf r)$ and $g_k = \mathrm{SubGain}(k,S_k,\mathbf r)/\mathrm{SubGain}(k,\mathcal M,\mathbf r)$, and suppose the types are ordered so that both $k \mapsto A_k$ and $k \mapsto g_k$ are nondecreasing. Let $\pi_k = g_k - g_{k-1}$ with $g_0 = 0$.
--
--   Mechanism 1 draws an index $k \in \{1, \dots, n\}$ with probability $\pi_k$, and offers only the grand set $\mathcal M$ at fee $A_k$, which is taken by exactly the types $i$ with $A_k \le A_i$; with the remaining probability $1 - \sum_k \pi_k$ nobody subscribes (the phantom index $n+1$). Its expected revenue is at least the planning's:
--   $$\sum_{i} q_i\big(p(S_i) + \lambda_i T\,\mathrm{Rent}(i,S_i,\mathbf r)\big) \le \sum_{k} \pi_k\, R(A_k) + \Big(1 - \sum_k \pi_k\Big) \sum_i q_i \lambda_i T\,\mathrm{Rent}(i,\emptyset,\mathbf r),$$
--   where $R(A_k) = \sum_i q_i\big[\mathbf 1\{A_k \le A_i\}\,(A_k + \lambda_i T\,\mathrm{Rent}(i,\mathcal M,\mathbf r)) + \mathbf 1\{A_k > A_i\}\,\lambda_i T\,\mathrm{Rent}(i,\emptyset,\mathbf r)\big]$ is the revenue of the grand subscription at fee $A_k$.
--
--   Since the right side is an average of the revenues of finitely many grand subscriptions, one of them earns at least the planning's revenue; this is the step from Mechanism 1 to Theorem 2.
--
--   **Formalization Note** The page claims, for an optimal planning, that each type's expected fee equals $p(S^*_i)$; that equality needs Lemma 4 and fails when the values $A_k$ tie. The statement is the inequality the conclusion uses, for every feasible planning. The ordering by $g$ within ties of $A$ is added (the page sorts by $A$ only and relies on Lemma 3 as printed); it makes $\pi$ a probability vector. Fees carry the factor $T$ of (3), which the page omits. The hypothesis $\mathbf r \ge 0$ is added.
-- source:
--   Alaei, Makhdoumi, Malekian, Optimal Subscription Planning for Digital Goods, working paper (SSRN 3476296; Operations Research, doi:10.1287/opre.2023.2468), p. 14, Mechanism 1 and the paragraph following it (proof pp. 33–34)

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting

namespace SubscriptionPlanning.GrandOptimal
theorem mechanism_1_revenue {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model n m Ω)
    (hM : M.Valid) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (hC : Condition2 M r)
    (p : Finset (Fin m) → ℝ) (S : Fin n → Finset (Fin m)) (hF : IsFeasible M r p S)
    (hsortA : Monotone (fun k : Fin n => M.lam k * subGain M k Finset.univ r))
    (hsortG : Monotone (fun k : Fin n => relGain M k (S k) r)) :
    revenue M r p S ≤
      ∑ k, lotteryWeight M r S k *
          grandRevenue M r (grandFee M r k) (fun i => decide (grandFee M r k ≤ grandFee M r i)) +
        (1 - ∑ k, lotteryWeight M r S k) * ∑ i, M.q i * (M.lam i * M.T * rent M i ∅ r) := by sorry
end SubscriptionPlanning.GrandOptimal
