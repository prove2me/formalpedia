-- Prove2me | Theorems.Thm_SuttonBartoRL_EpsSoft_eps_greedy_improvement
-- name    : SuttonBartoRL.EpsSoft.eps_greedy_improvement
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:00:35.271009+00:00
-- url     : https://prove2.me/theorems/851767d8-adaa-421c-ba9b-3d7d795d7d0a
-- title:
--   ε-greedy policy improvement: v_π′ ≥ v_π, with equality only when π and π′ are optimal among ε-soft policies
-- statement:
--   Let a finite MDP be given with discount rate $0 \le \gamma < 1$ and let $0 < \varepsilon \le 1$. Let $\pi$ be an $\varepsilon$-soft policy and $\pi'$ any $\varepsilon$-greedy policy with respect to $q_\pi$. Then:
--
--   1. $\pi'$ is better than or equal to $\pi$:
--   $$
--   v_{\pi'}(s) \ge v_\pi(s) \qquad \text{for all } s \in \mathcal S;
--   $$
--   2. if $v_{\pi'}(s) = v_\pi(s)$ for all $s$, then both $\pi'$ and $\pi$ are optimal among the $\varepsilon$-soft policies: they are $\varepsilon$-soft and better than or equal to every $\varepsilon$-soft policy.
--
--   This is the statement that policy iteration works for $\varepsilon$-soft policies: each $\varepsilon$-greedy step improves the policy, except when the best policy among the $\varepsilon$-soft policies has already been found. It is the dynamic-programming content of on-policy Monte Carlo control without exploring starts, and it holds whatever the method used to compute $q_\pi$, provided it is computed exactly.
--
--   **Formalization Note** The action set is one finite nonempty set for all states, so $|\mathcal A(s)| = |\mathcal A|$. "Any $\varepsilon$-greedy policy" is encoded by quantifying over every choice of greedy action at every state. $v_\pi$ is the expected discounted return with $0 \le \gamma < 1$. The book's condition "for some $\varepsilon > 0$" and $\varepsilon \le 1$ (without which no $\varepsilon$-soft policy exists) are explicit hypotheses.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.4, pp. 101–102 ('For any ε-soft policy, π, any ε-greedy policy with respect to q_π is guaranteed to be better than or equal to π', p. 101; 'equality can hold only when both π′ and π are optimal among the ε-soft policies', p. 102)

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_EpsSoftPolicies

namespace SuttonBartoRL.EpsSoft

/-- pp. 101–102: for a finite MDP with `0 ≤ γ < 1` and `0 < ε ≤ 1`, if `π` is `ε`-soft and `π'` is
any `ε`-greedy policy with respect to `q_π`, then `v_{π'}(s) ≥ v_π(s)` for all states `s`; and if
`v_{π'} = v_π`, then both `π'` and `π` are optimal among the `ε`-soft policies. -/
theorem eps_greedy_improvement {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (π π' : SuttonBartoRL.FiniteMDP.Policy S A) (hπ : IsEpsSoft ε π)
    (hπ' : IsEpsGreedy M γ ε π π') :
    (∀ s, stateValue M γ π s ≤ stateValue M γ π' s) ∧
      ((∀ s, stateValue M γ π' s = stateValue M γ π s) →
        IsOptimalAmongEpsSoft M γ ε π' ∧ IsOptimalAmongEpsSoft M γ ε π) := by sorry

end SuttonBartoRL.EpsSoft
