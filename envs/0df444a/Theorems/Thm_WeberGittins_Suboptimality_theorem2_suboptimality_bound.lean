-- Prove2me | Theorems.Thm_WeberGittins_Suboptimality_theorem2_suboptimality_bound
-- name    : WeberGittins.Suboptimality.theorem2_suboptimality_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:11.182823+00:00
-- url     : https://prove2.me/theorems/3c06f6ec-9c5a-4c40-b9aa-683742392f9c
-- title:
--   Theorem 2 — V_{π*}(x) − V_π(x) ≤ (1 − β)E_π[Σ_t β^t(max_i min_{s≤t} G_i(x_i(s)) − R_{j(t)}/(1 − β))]
-- statement:
--   Consider the discounted $k$-armed Markov bandit with state space $S$ (a standard Borel space), Markov kernel $P$, measurable reward $r$ that is nonnegative and uniformly bounded, and discount factor $0<\beta<1$. Let $\gamma$ be the fair charge and
--   $$G(y) = \frac{\gamma(y)}{1-\beta}$$
--   the Gittins index of Weber's (3). Write $x_i(t)$ for the state of bandit $i$ at time $t$, $j(t)$ for the bandit played at time $t$, and $V_\pi(x)$ for the expected total discounted reward (1) of a policy $\pi$ from the initial states $x$.
--
--   Suppose $\pi^*$ is the optimal (Gittins) policy, i.e. a policy that in every round plays, with probability one, an arm of greatest Gittins index. Then for every policy $\pi$ and every initial state vector $x$,
--   $$V_{\pi^*}(x) - V_\pi(x) \;\le\; (1-\beta) \sum_{t=0}^\infty \beta^t\, \mathbb{E}_\pi\Big[\max_i \min_{0\le s\le t} G\big(x_i(s)\big) - \frac{r\big(x_{j(t)}(t)\big)}{1-\beta} \,\Big|\, x(0)=x\Big].$$
--
--   This is Theorem 2 of the paper, inequality (6), a bound first given by Glazebrook (1990). It measures how far an arbitrary policy falls short of the optimum by the expected discounted excess, along the policy's own trajectory, of the greatest prevailing charge over the reward actually collected.
--
--   **Formalization Note** Since $G = \gamma/(1-\beta)$, the bound is equivalent to $V_{\pi^*}(x) - V_\pi(x) \le \sum_t \beta^t E_\pi[\max_i \min_{s\le t}\gamma(x_i(s)) - r(x_{j(t)}(t))]$; the statement keeps the paper's form, with $G$ inside and the factor $1-\beta$ outside. "The optimal (Gittins) policy" is any policy satisfying the published `IsGittinsIndexPolicy` (its optimality is the published Theorem 1, `BanditAlgorithm.gittins_index_theorem`); the statement does not assume one exists. Weber's $E_\pi[\sum_t \beta^t(\cdot)]$ is written as the series of round expectations, which agrees with it for bounded rewards. At round $t$ the integrand is evaluated on the history of the first $t$ rounds and the current state vector $x(t)$, so the minimum runs over $s = 0,\dots,t$; $r$ is the mean of Weber's random reward $R_j$. The hypotheses "rewards nonnegative and uniformly bounded" and $0<\beta<1$ are the standing assumptions of Section 1; measurability of $r$ and the standard Borel structure on $S$ are added regularity. The bandits are indexed by $\mathrm{Fin}\,k$; when $k=0$ no policy exists, so the statement has content only for $k \ge 1$.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1029, Theorem 2, eq. (6)

import Definitions.Def_WeberGittins_Suboptimality_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.Suboptimality
theorem theorem2_suboptimality_bound {k : ℕ} {S : Type*}
    [MeasurableSpace S] [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (πstar : MarkovBanditPolicy k S) (hπstar : IsGittinsIndexPolicy P r β πstar)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditDiscountedValue P r β πstar x - markovBanditDiscountedValue P r β π x ≤
      (1 - β) * ∑' t : ℕ, β ^ t * roundExpectation P π x t (fun h j =>
        (⨆ i : Fin k, currentHistoryPrevailingCharge (weberIndex P r β) t h i) -
          r (h.2 j) / (1 - β)) := by sorry
end WeberGittins.Suboptimality
