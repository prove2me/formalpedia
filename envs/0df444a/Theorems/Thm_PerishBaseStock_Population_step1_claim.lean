-- Prove2me | Theorems.Thm_PerishBaseStock_Population_step1_claim
-- name    : PerishBaseStock.Population.step1_claim
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:40.228982+00:00
-- url     : https://prove2.me/theorems/4ca52835-250f-4c03-aad0-440419d16a0f
-- title:
--   Step-1 claim — for every $k>1$, $S^{NP}_n\le k\mu n$ for all large $n$
-- statement:
--   Let the generic one-period demand be $D(n)=\sum_{j=1}^{N(n)}\hat D_j$ of the population form (7), with $\mu=\mathbb E[\hat D_1]>0$, and let $S^{NP}_n=F_n^{-1}(p/(p+h))$ be its newsvendor level ($h>0$, $p>0$). For every fixed $k>1$ there is a positive integer $n_1(k)$ such that
--   $$
--   S^{NP}_n\le k\mu n\qquad\text{for every } n\ge n_1(k).
--   $$
--
--   The newsvendor level of the population demand grows no faster than its mean, which is of order $\mu n$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec3, App. B.1, first step

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Population

/-- **Step-1 claim** (Bu, Gong & Chao, App. B.1, p. ec3). With demand of form (7), for any fixed
`k > 1` there is `n₁(k) > 0` such that `S^NP_n ≤ k μ n` for every `n ≥ n₁(k)`, where
`μ = E[D̂_1]`. -/
theorem step1_claim (c : PerishBaseStock.Lifetime.Params) (Dh : CustomerLaw) (X : InterarrivalLaw)
    (hμ : 0 < customerMean Dh)
    (P : ℕ → CappedBaseStock.DemandLaw) (hP : IsPopulationFamily Dh X P)
    (k : ℝ) (hk : 1 < k) :
    ∃ n₁ : ℕ, 0 < n₁ ∧ ∀ n : ℕ, n₁ ≤ n →
      (newsvendorLevel (P n) c : ℝ) ≤ k * customerMean Dh * (n : ℝ) := by sorry

end PerishBaseStock.Population
