-- Prove2me | Theorems.Thm_WeberGittins_IndexGap_switch_to_gittins_after_t_optimal
-- name    : WeberGittins.IndexGap.switch_to_gittins_after_t_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:23.669081+00:00
-- url     : https://prove2.me/theorems/d72e7844-3e9a-4a9e-8554-dfda4af0512c
-- title:
--   Proof of Theorem 3, p. 1029 — $V_{\pi(t)}(x)\le V_{\pi^*(t+1)}(x)$: switching to Gittins after time $t$ never lowers the value
-- statement:
--   Consider the discounted $k$-armed Markov bandit with state space $S$ (a standard Borel space), transition kernel $P$, measurable mean reward $r$ that is nonnegative and uniformly bounded, and discount factor $0 < \beta < 1$. For a policy $\sigma$ and initial state vector $x$ write
--   $$V_\sigma(x) = E_\sigma\Big[\sum_{t=0}^\infty \beta^t r\big(x_{j(t)}(t)\big) \,\Big|\, x(0) = x\Big]$$
--   for its expected total-discounted reward, as in (1).
--
--   Let $\sigma$ be any policy, $t \ge 0$, and let $\sigma'$ be a policy that is identical to $\sigma$ through time $t$ (the same selection rule in every round $n \le t$) and is a Gittins index policy in every round $n \ge t+1$ (it plays, almost surely, an arm of greatest current fair charge, ties broken arbitrarily). Then
--   $$V_\sigma(x) \le V_{\sigma'}(x).$$
--
--   Weber uses this with $\sigma = \pi(t)$ and $\sigma' = \pi^*(t+1)$: "since $\pi(t)$ and $\pi^*(t+1)$ are identical through time $t$ and $\pi^*(t+1)$ is optimal thereafter, $V_{\pi(t)}(x) \le V_{\pi^*(t+1)}(x)$". It is the step that lets the bounds (8) for consecutive $t$ telescope into Theorem 3. For $t$ replaced by the start of play it is the optimality of the Gittins index policy (Theorem 1 of the paper, already on Prove2Me as `BanditAlgorithm.gittins_index_theorem`).
--
--   **Formalization Note** The statement is the general form of the sentence ("$\pi^*(t+1)$ is optimal thereafter"): $\sigma$ is arbitrary, not only $\pi(t)$. The hypothesis on $\sigma'$ is `IsSwitchToGittinsAt P r β σ (t + 1) σ'`. Weber's $n$ bandits with their own state spaces are encoded as $k$ chains on one state space with one kernel and one reward (take the disjoint union); $r$ is the conditional mean of the random reward $R_j$. The value is the series of discounted round expectations, the published convention. The standing assumptions of Section 1 (bounded nonnegative rewards, $0<\beta<1$) are hypotheses; measurability of $r$ and the standard Borel structure of $S$ are regularity hypotheses the paper leaves implicit.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1029, proof of Theorem 3, last paragraph ("Note that since π(t) and π*(t + 1) are identical through time t …")

import Definitions.Def_GittinsIndex
import Definitions.Def_WeberGittins_IndexGap_SwitchPolicies

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.IndexGap

theorem switch_to_gittins_after_t_optimal {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (σ σ' : MarkovBanditPolicy k S) (t : ℕ) (hσ' : IsSwitchToGittinsAt P r β σ (t + 1) σ')
    (x : Fin k → S) :
    markovBanditDiscountedValue P r β σ x ≤ markovBanditDiscountedValue P r β σ' x := by sorry

end WeberGittins.IndexGap
