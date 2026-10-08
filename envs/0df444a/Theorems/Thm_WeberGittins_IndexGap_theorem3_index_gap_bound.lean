-- Prove2me | Theorems.Thm_WeberGittins_IndexGap_theorem3_index_gap_bound
-- name    : WeberGittins.IndexGap.theorem3_index_gap_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:12.57229+00:00
-- url     : https://prove2.me/theorems/5e74b1b1-7208-4b31-b2ce-1da8a6caeedd
-- title:
--   Theorem 3 — $V_{\pi^*}(x)-V_\pi(x)\le E_\pi[\sum_t\beta^t(\max_iG_i(x_i(t))-G_{j(t)}(x_{j(t)}(t)))]$
-- statement:
--   Consider $k$ bandit processes, each a Markov chain on a standard Borel state space $S$ with transition kernel $P$. In each round $t = 0, 1, 2, \dots$ a gambler plays one bandit $j(t)$, collects a reward with mean $r(x_{j(t)}(t))$, and only the played bandit changes state. Rewards are nonnegative and uniformly bounded, $r$ is measurable, and the discount factor satisfies $0<\beta<1$. The value of a policy $\pi$ from the initial state vector $x$ is
--   $$V_\pi(x) = E_\pi\Big[\sum_{t=0}^\infty \beta^t r\big(x_{j(t)}(t)\big) \,\Big|\, x(0)=x\Big].$$
--   Let $\gamma(y)$ be the fair charge of state $y$ (the supremum over stopping times $\tau \ge 1$ of expected discounted reward over expected discounted time) and $G(y) = \gamma(y)/(1-\beta)$ the Gittins index.
--
--   **Theorem 3.** Let $\pi^*$ be a Gittins index policy (one that always plays a bandit of greatest Gittins index, ties broken arbitrarily), and let $\pi$ be any policy. Then
--   $$V_{\pi^*}(x) - V_\pi(x) \le E_\pi\left[\sum_{t=0}^\infty \beta^t\Big(\max_i G_i\big(x_i(t)\big) - G_{j(t)}\big(x_{j(t)}(t)\big)\Big) \,\middle|\, x(0)=x\right].$$
--
--   The suboptimality of an arbitrary policy is thus bounded by the expected discounted sum, along its own trajectory, of the amounts by which the index of the bandit it plays falls short of the greatest index. A policy that plays a bandit within $\varepsilon$ of the greatest index in every round therefore loses at most $\varepsilon/(1-\beta)$.
--
--   **Formalization Note** "$\pi^*$ is the optimal (Gittins) policy" is read as: $\pi^*$ is any policy with `IsGittinsIndexPolicy P r β πstar`, as in the published Theorem 1. The expectation of the series is written as the series of round expectations, $\sum_t \beta^t E_\pi[\,\cdot\,]$, the convention of the published value; under bounded rewards the two agree. The index is Weber's $G$ (`weberIndex`), not the fair charge $\gamma$ (`gittinsIndex`); with $\gamma$ the bound would be false by the factor $1-\beta$. The hypothesis that $\gamma$ is measurable is added so that the expectation is a genuine integral. The standing assumptions of Section 1 and the regularity hypotheses (measurable $r$, standard Borel $S$) are binders; Weber's bandits with separate state spaces are encoded on one state space (disjoint union).
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1029, Theorem 3, eq. (7)

import Definitions.Def_GittinsIndex
import Definitions.Def_WeberGittins_IndexGap_SwitchPolicies

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.IndexGap

theorem theorem3_index_gap_bound {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (πstar : MarkovBanditPolicy k S) (hπstar : IsGittinsIndexPolicy P r β πstar)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditDiscountedValue P r β πstar x - markovBanditDiscountedValue P r β π x ≤
      ∑' t : ℕ, β ^ t * WeberGittins.Suboptimality.roundExpectation P π x t (fun h j =>
        (⨆ i : Fin k, WeberGittins.Suboptimality.weberIndex P r β (h.2 i)) - WeberGittins.Suboptimality.weberIndex P r β (h.2 j)) := by sorry

end WeberGittins.IndexGap
