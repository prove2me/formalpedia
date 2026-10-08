-- Prove2me | Theorems.Thm_WeberGittins_Suboptimality_gittins_value_eq_discounted_greatest_prevailing_charge
-- name    : WeberGittins.Suboptimality.gittins_value_eq_discounted_greatest_prevailing_charge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:06.251672+00:00
-- url     : https://prove2.me/theorems/f7b35a60-6756-4daa-864a-4359eb8d7f64
-- title:
--   Proof of Theorem 1, pp. 1026–1027 — the Gittins policy's value equals its expected discounted greatest prevailing charge
-- statement:
--   Consider the discounted $k$-armed Markov bandit with state space $S$ (a standard Borel space), Markov kernel $P$, measurable reward $r$ that is nonnegative and uniformly bounded, and discount factor $0<\beta<1$. Let $\gamma$ be the fair charge, and let $\pi^*$ be a Gittins index policy: in every round it plays, with probability one, an arm whose current state has the greatest fair charge (ties broken arbitrarily). Write $V_{\pi^*}(x)$ for its expected total discounted reward (1) from the initial states $x$.
--
--   Then
--   $$V_{\pi^*}(x) \;=\; \sum_{t=0}^\infty \beta^t\, \mathbb{E}_{\pi^*}\Big[\max_i \min_{0\le s\le t} \gamma\big(x_i(s)\big) \,\Big|\, x(0)=x\Big].$$
--
--   The right-hand side is the expected discounted greatest prevailing charge. Under the Gittins policy the bandit played at time $t$ is one of greatest prevailing charge, so this is the expected discounted charge the gambler pays; the identity says that the bound (5) holds with equality for the Gittins policy ("By the second remark, this bound is achieved by the proposed policy").
--
--   **Formalization Note** "The proposed policy" is any policy satisfying the published `IsGittinsIndexPolicy`; the statement does not assume one exists. $E_\pi[\sum_t \beta^t(\cdot)]$ is written as the series of round expectations, the convention of the published value. The inner quantity at round $t$ is evaluated on the history of the first $t$ rounds together with the current state vector $x(t)$, so the minimum covers times $0,\dots,t$. The standing assumptions of Weber's Section 1 (nonnegative bounded rewards, $0<\beta<1$) are hypotheses; measurability of $r$ and the standard Borel structure on $S$ are added regularity. The finite-horizon version, with the terminal retirement potential, is the second conjunct of the published `BanditAlgorithm.gittins_finite_prevailing_charge_accounting`, and the potential's vanishing is `BanditAlgorithm.tendsto_gittins_terminal_retirement_potential_zero`.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), pp. 1026–1027, proof of Theorem 1 (Remark 2 and the paragraph after it)

import Definitions.Def_WeberGittins_Suboptimality_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.Suboptimality
theorem gittins_value_eq_discounted_greatest_prevailing_charge {k : ℕ} {S : Type*}
    [MeasurableSpace S] [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (πstar : MarkovBanditPolicy k S) (hπstar : IsGittinsIndexPolicy P r β πstar)
    (x : Fin k → S) :
    markovBanditDiscountedValue P r β πstar x =
      ∑' t : ℕ, β ^ t * roundExpectation P πstar x t (fun h _ =>
        ⨆ i : Fin k, currentHistoryPrevailingCharge (gittinsIndex P r β) t h i) := by sorry
end WeberGittins.Suboptimality
