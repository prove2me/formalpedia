-- Prove2me | Theorems.Thm_PerishBaseStock_LifoNegative_cyclic_policy_cost
-- name    : PerishBaseStock.LifoNegative.cyclic_policy_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T04:28:21.523282+00:00
-- url     : https://prove2.me/theorems/e53eff9d-f355-4931-9c0c-eb0c4d11ae9a
-- title:
--   App. C.3, p. ec9 — the cyclic policy is admissible and its cost is $<p(\mathbb E[D]-\underline D)$ and independent of $\theta$
-- statement:
--   Consider the LIFO system with lifetime $m \ge 2$, costs $h, p > 0$, and a demand law with $S^{NP} > \underline D > 0$. Let $\pi^c$ be the policy that orders $\min\{S^{NP}, m\underline D\}$ units in periods $1, m+1, 2m+1, \dots$ and uses the base-stock policy with level $\underline D$ in all other periods. Then:
--   1. $\pi^c$ is admissible: its order in each period is a measurable function of the current state;
--   2. its long-run average cost $C^{\pi^c}_\theta$ does not depend on the outdating cost $\theta \ge 0$;
--   3. it is strictly below the limit of the best base-stock cost:
--   $$C^{\pi^c} < p(\mathbb E[D] - \underline D).$$
--
--   This is the construction behind Proposition 1: a policy that is not base-stock beats every base-stock policy for large $\theta$.
--
--   **Formalization Note** Item 1 is the paper's "admissible policy" (ec8); items 2–3 are the sentence of ec9. Independence of $\theta$ is stated as equality of the cost for every $\theta \ge 0$ with the cost at the structure's own $\theta$. The cost is in $[0,\infty]$, so the strict inequality also asserts finiteness.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), pp. ec8–ec9, App. C.3 (Proof of Proposition 1), the cyclic policy and the sentence 'Combining these results together …'

import Definitions.Def_PerishBaseStock_LifoNegative_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.LifoNegative

theorem cyclic_policy_cost (P : DemandLaw) (c : Params) (hm : 2 ≤ c.m)
    (hNP : PerishBaseStock.Outdating.lowerSupport P < (newsvendorLevel P.law c.h c.p : ℝ))
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) :
    (∀ t, Measurable (cyclicOrder P c t)) ∧
    (∀ θ : ℝ≥0, longRunCost P (c.withTheta θ) (cyclicOrder P c) =
      longRunCost P c (cyclicOrder P c)) ∧
    longRunCost P c (cyclicOrder P c) < ENNReal.ofReal (c.p * (mean P - PerishBaseStock.Outdating.lowerSupport P)) := by sorry

end PerishBaseStock.LifoNegative
