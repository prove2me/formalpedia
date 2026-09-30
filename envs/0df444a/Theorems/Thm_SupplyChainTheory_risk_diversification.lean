-- Prove2me | Theorems.Thm_SupplyChainTheory_risk_diversification
-- name    : SupplyChainTheory.risk_diversification
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:49:47.265988+00:00
-- url     : https://prove2.me/theorems/0e34ea8c-9c01-49fe-8633-102d75eb981f
-- title:
--   Theorem 9.9 (the risk-diversification effect): $S^*_C = NS^*$, $g^*_C = g^*_D = Ng^*$, $V^*_C = NV^*_D = N^2V^*$
-- statement:
--   **Theorem 9.9.** Consider $N$ distribution centers, each facing deterministic demand $d$ per
--   period and supply disruptions with disruption probability $\alpha$ and recovery probability
--   $\beta$, each following the base-stock policy of Sect. 9.2.2 with costs $h, p > 0$, and the
--   centralized single center formed by merging them, which faces demand $Nd$. Let $S^*$, $g^*$ and
--   $V^*$ be the optimal base-stock level, expected cost and cost variance of a single center. Then
--
--   1. $S^*_C = NS^*_D = NS^*$: the centralized optimal level is $N$ times the single-center level,
--      so the total inventory is the same in both systems;
--   2. $g^*_C = g^*_D = Ng^*$: the expected cost of the centralized center at its optimal level is
--      $N$ times the single-center cost, the same as the decentralized total;
--   3. $V^*_C = NV^*_D = N^2V^*$: the cost variance of the centralized center is $N^2 V^*$, while the
--      decentralized total, a sum of $N$ independent single-center costs, has variance $NV^*$.
--
--   Centralization does not change the expected cost but multiplies the variance by $N$: under
--   supply uncertainty, disruptions in the centralized system are as frequent but $N$ times as
--   severe. This is the risk-diversification effect (Snyder and Shen 2006), the mirror image of the
--   risk-pooling effect of Chapter 7, and it is why a risk-averse planner prefers the decentralized
--   system.
--
--   **Formalization Note** The statement is about the single-center functions under the scaling
--   $d \mapsto Nd$, $S \mapsto NS$: an optimal level for $d$ scales to an optimal level for $Nd$, the
--   expected cost scales by $N$ and the variance by $N^2$. The decentralized totals $Ng^*$ and $NV^*$
--   are the mean and variance of a sum of $N$ independent copies, which the book takes as given.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 386, Sect. 9.5.4, Theorem 9.9 and the derivation (9.55)-(9.59); after Schmitt et al. (2015) and Snyder and Shen (2006)

import Definitions.Def_SupplyChainTheory_disruptions

namespace SupplyChainTheory

theorem risk_diversification (α β h p d : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hh : 0 < h) (hp : 0 < p) (hd : 0 < d) (N : ℕ) (hN : 0 < N) (S : ℝ) :
    (IsMinOn (meanCost α β h p d) Set.univ S → IsMinOn (meanCost α β h p (N * d)) Set.univ (N * S))
      ∧ meanCost α β h p (N * d) (N * S) = N * meanCost α β h p d S
      ∧ varCost α β h p (N * d) (N * S) = (N : ℝ) ^ 2 * varCost α β h p d S := by sorry

end SupplyChainTheory
