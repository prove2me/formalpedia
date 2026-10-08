-- Prove2me | Theorems.Thm_WeberGittins_Suboptimality_eq5_value_le_discounted_prevailing_charge
-- name    : WeberGittins.Suboptimality.eq5_value_le_discounted_prevailing_charge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:03.187134+00:00
-- url     : https://prove2.me/theorems/c1ba8b0b-5a2f-4c2e-a4cf-1b99ca561092
-- title:
--   Eq. (5) — the discounted reward of any policy is at most its expected discounted prevailing charge
-- statement:
--   Consider the discounted $k$-armed Markov bandit with state space $S$ (a standard Borel space), Markov kernel $P$, measurable reward $r$ that is nonnegative and uniformly bounded, and discount factor $0 < \beta < 1$. For an arm $j$ and a time $t$, the **prevailing charge** of $j$ at $t$ is the least fair charge seen so far on that arm,
--   $$\min_{0 \le s \le t} \gamma\big(x_j(s)\big),$$
--   where $\gamma$ is the fair charge (Gittins index in the ratio form (4)) and $x_j(s)$ is the state of arm $j$ at time $s$. Write $j(t)$ for the arm played at time $t$ and $V_\pi(x)$ for the expected total discounted reward (1) of the policy $\pi$ from the initial states $x$.
--
--   Then for every policy $\pi$ and every initial state vector $x$,
--   $$V_\pi(x) \;\le\; \sum_{t=0}^\infty \beta^t\, \mathbb{E}_\pi\Big[\min_{0\le s\le t} \gamma\big(x_{j(t)}(s)\big) \,\Big|\, x(0)=x\Big].$$
--
--   This is Weber's equation (5): the expected discounted reward of any policy is bounded by the expected discounted charges it incurs, when each play of an arm is charged that arm's prevailing charge. It is the first half of the accounting behind both the Gittins index theorem and the suboptimality bound of Theorem 2.
--
--   **Formalization Note** Weber writes $E_\pi[\sum_t \beta^t (\cdot)]$; the statement uses the series of round expectations $\sum_t \beta^t E_\pi[\cdot]$, the convention of the published value $V_\pi$; the two agree for bounded rewards. The round-$t$ prevailing charge is the published `markovBanditRoundPrevailingCharge`, whose minimum runs over the states of the played arm at times $0,\dots,t$. The hypotheses "rewards nonnegative and uniformly bounded" and $0<\beta<1$ are Weber's standing assumptions of Section 1; measurability of $r$ and the standard Borel structure on $S$ are regularity conditions the paper leaves implicit. The finite-horizon version is the first conjunct of the published `BanditAlgorithm.gittins_finite_prevailing_charge_accounting`.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1028, Section 5, eq. (5) (from Remark 1, p. 1026)

import Definitions.Def_GittinsPrevailingChargeValue
import Definitions.Def_WeberGittins_Suboptimality_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.Suboptimality
theorem eq5_value_le_discounted_prevailing_charge {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditDiscountedValue P r β π x ≤
      ∑' t : ℕ, β ^ t * markovBanditRoundPrevailingCharge P r β π x t := by sorry
end WeberGittins.Suboptimality
