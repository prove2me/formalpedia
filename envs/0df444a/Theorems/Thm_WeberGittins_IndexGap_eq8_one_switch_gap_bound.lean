-- Prove2me | Theorems.Thm_WeberGittins_IndexGap_eq8_one_switch_gap_bound
-- name    : WeberGittins.IndexGap.eq8_one_switch_gap_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:18.064978+00:00
-- url     : https://prove2.me/theorems/df742747-08db-4552-adc8-a640f67288ae
-- title:
--   Proof of Theorem 3, eq. (8) — $V_{\pi^*(t)}(x)-V_{\pi(t)}(x)\le\beta^tE_\pi[(\max_i\gamma_i(x_i(t))-\gamma_{j(t)}(x_{j(t)}(t)))/(1-\beta)]$
-- statement:
--   Consider the discounted $k$-armed Markov bandit with state space $S$ (a standard Borel space), transition kernel $P$, measurable mean reward $r$ that is nonnegative and uniformly bounded, and discount factor $0<\beta<1$. Let $\gamma_i(y)$ be the fair charge of arm $i$ in state $y$ (the ratio (4)), and $V_\sigma(x)$ the expected total-discounted reward (1) of a policy $\sigma$ from the initial state vector $x$.
--
--   Let $\pi$ be an arbitrary policy and $t \ge 0$. Let $\pi^*(t)$ be any policy identical to $\pi$ in rounds $n < t$ and a Gittins index policy in rounds $n \ge t$, and let $\pi(t)$ be any policy identical to $\pi$ in rounds $n \le t$ which then continues playing the arm $j(t)$ until its fair charge drops below $\gamma_{j(t)}(x_{j(t)}(t))$ and is a Gittins index policy thereafter (the definitions `SwitchPolicies`). Then
--   $$V_{\pi^*(t)}(x) - V_{\pi(t)}(x) \le \beta^t E_\pi\left[\frac{\max_i \gamma_i(x_i(t)) - \gamma_{j(t)}\big(x_{j(t)}(t)\big)}{1-\beta} \,\middle|\, x(0) = x\right].$$
--
--   The expectation is under $\pi$; since $\pi$, $\pi^*(t)$ and $\pi(t)$ agree before time $t$, and $\pi(t)$ agrees with $\pi$ at time $t$, it is equally the expectation under $\pi(t)$. The bound charges a single deviation from the Gittins rule at time $t$ by the gap, at that time, between the greatest fair charge and the fair charge of the arm played. Summing it over $t$ gives Theorem 3.
--
--   **Formalization Note** The statement holds for every pair of policies satisfying the predicates `IsSwitchToGittinsAt P r β π t` and `IsRunThenGittinsAt P r β π t`. The expectation is the round-$t$ expectation `roundExpectation P π x t` of the integrand evaluated at the states $x(t)$ and the arm $j(t)$ played in round $t$; $\max_i$ is a supremum over the $k$ arms ($k \ge 1$ whenever a policy exists). The hypothesis that $y \mapsto \gamma(y)$ is measurable is added so that this expectation is a genuine integral; the paper takes it for granted. The standing assumptions of Section 1 (bounded nonnegative rewards, $0<\beta<1$), measurability of $r$ and the standard Borel structure of $S$ are hypotheses; the encoding of the bandits on one state space is as in the published model.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1029, proof of Theorem 3, eq. (8)

import Definitions.Def_GittinsIndex
import Definitions.Def_WeberGittins_IndexGap_SwitchPolicies

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.IndexGap

theorem eq8_one_switch_gap_bound {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (π : MarkovBanditPolicy k S) (t : ℕ) (σstar σ : MarkovBanditPolicy k S)
    (hσstar : IsSwitchToGittinsAt P r β π t σstar) (hσ : IsRunThenGittinsAt P r β π t σ)
    (x : Fin k → S) :
    markovBanditDiscountedValue P r β σstar x - markovBanditDiscountedValue P r β σ x ≤
      β ^ t * WeberGittins.Suboptimality.roundExpectation P π x t (fun h j =>
        ((⨆ i : Fin k, gittinsIndex P r β (h.2 i)) - gittinsIndex P r β (h.2 j)) / (1 - β)) := by sorry

end WeberGittins.IndexGap
