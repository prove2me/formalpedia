-- Prove2me | Theorems.Thm_WeberGittins_Suboptimality_greatest_prevailing_charge_ge_gittins
-- name    : WeberGittins.Suboptimality.greatest_prevailing_charge_ge_gittins
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:14.994966+00:00
-- url     : https://prove2.me/theorems/9d50b950-f8e7-4d65-9c54-bea745c1a22e
-- title:
--   Section 5, p. 1028 — on a fixed realisation, any policy's greatest prevailing charge is at least the Gittins policy's
-- statement:
--   Fix a realisation of the states through which each of $k$ bandits evolves. Along it, the prevailing charge of bandit $i$ after it has been played $m$ times is a number $H_i(m)$, and $m \mapsto H_i(m)$ is nonincreasing (it is a running minimum of fair charges). A policy, on this realisation, is a sequence of arms $a(0), a(1), \dots$; write
--   $$n_i^a(t) = \#\{\, s < t : a(s) = i \,\}$$
--   for the number of plays of bandit $i$ before time $t$, so that $H_i(n_i^a(t))$ is the prevailing charge of bandit $i$ at time $t$. The Gittins policy plays, at every time, a bandit whose current prevailing charge is greatest: $a^*$ is a sequence with $H_i(n_i^{a^*}(t)) \le H_{a^*(t)}(n_{a^*(t)}^{a^*}(t))$ for all $i$ and $t$.
--
--   Then for every sequence $a$ and every time $t$,
--   $$\max_i H_i\big(n_i^{a^*}(t)\big) \;\le\; \max_i H_i\big(n_i^{a}(t)\big).$$
--
--   In words: if one follows a policy that differs from the Gittins policy, the greatest prevailing charge at time $t$ is at least as great as it would have been under the Gittins policy. Combined with (5), this gives the suboptimality bound of Theorem 2.
--
--   **Formalization Note** The statement is deterministic. The paper's "fixed realisation" is encoded by arbitrary nonincreasing sequences $H_i : \mathbb{N} \to \mathbb{R}$ (the prevailing-charge stacks, which along a realisation are $m \mapsto \min_{l \le m} \gamma_i(\omega_i(l))$), and "the Gittins policy" by any greedy interleaving of these stacks (the published `IsGreedyChargeStackInterleaving`, ties broken arbitrarily). The statement is proved for all nonincreasing stacks, which include the running-minimum stacks. The play counts are the published `stackPullCountBefore`. Bandits are indexed by $\mathrm{Fin}\,k$; at $k = 0$ both maxima are the empty supremum $0$.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1028, Section 5, the paragraph after eq. (5)

import Definitions.Def_GittinsChargeInterleaving

open BanditAlgorithm

namespace WeberGittins.Suboptimality
theorem greatest_prevailing_charge_ge_gittins {k : ℕ} (H : Fin k → ℕ → ℝ)
    (hH : ∀ i, Antitone (H i)) (astar : ℕ → Fin k)
    (hastar : IsGreedyChargeStackInterleaving H astar) (a : ℕ → Fin k) (t : ℕ) :
    (⨆ i : Fin k, H i (stackPullCountBefore astar i t)) ≤
      ⨆ i : Fin k, H i (stackPullCountBefore a i t) := by sorry
end WeberGittins.Suboptimality
