-- Prove2me | Theorems.Thm_SuttonBartoRL_EpsSoft_policy_improvement_stochastic
-- name    : SuttonBartoRL.EpsSoft.policy_improvement_stochastic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:38:39.51708+00:00
-- url     : https://prove2.me/theorems/13ce78d4-c3bf-48a0-a44e-8b9302017263
-- title:
--   Policy improvement theorem (4.7)–(4.8) for stochastic policies
-- statement:
--   Let a finite MDP be given with discount rate $0 \le \gamma < 1$, and let $\pi$, $\pi'$ be stochastic policies. Write $q_\pi(s, \pi'(s)) = \sum_a \pi'(a \mid s)\, q_\pi(s, a)$ for the value of choosing the first action according to $\pi'$ and following $\pi$ thereafter. If
--   $$
--   q_\pi(s, \pi'(s)) \ge v_\pi(s) \qquad \text{for all } s \in \mathcal S, \tag{4.7}
--   $$
--   then
--   $$
--   v_{\pi'}(s) \ge v_\pi(s) \qquad \text{for all } s \in \mathcal S. \tag{4.8}
--   $$
--   Moreover, if (4.7) is strict at some state, then (4.8) is strict at that state.
--
--   This is the engine of policy iteration; in this mission it turns the one-step inequality (5.2) for $\varepsilon$-greedy policies into improvement of the whole value function.
--
--   **Formalization Note** The book states the theorem for deterministic policies (p. 78) and says it "carries through as stated for the stochastic case" (p. 79); this is that stochastic statement, with $0 \le \gamma < 1$ (the book's standing assumption for the existence of $v_\pi$, p. 74). The same statement is drafted in the chapter-4 mission of this series; drafts cannot import drafts, so it is restated here.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, policy improvement theorem (4.7)–(4.8), p. 78; stochastic case, p. 79; applied in §5.4, p. 102

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_ValueFunctions

namespace SuttonBartoRL.EpsSoft

/-- Policy improvement theorem (4.7)–(4.8), p. 78, for stochastic policies ("the policy improvement
theorem carries through as stated for the stochastic case", p. 79). For a finite MDP and
`0 ≤ γ < 1`: if `q_π(s, π'(s)) := Σ_a π'(a | s) q_π(s, a) ≥ v_π(s)` for every state `s`, then
`v_{π'}(s) ≥ v_π(s)` for every `s`; moreover, strict inequality in (4.7) at a state gives strict
inequality in (4.8) at that state. -/
theorem policy_improvement_stochastic {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π π' : SuttonBartoRL.FiniteMDP.Policy S A)
    (h : ∀ s, stateValue M γ π s ≤ ∑ a, π'.prob s a * actionValue M γ π s a) :
    (∀ s, stateValue M γ π s ≤ stateValue M γ π' s) ∧
      (∀ s, stateValue M γ π s < ∑ a, π'.prob s a * actionValue M γ π s a →
        stateValue M γ π s < stateValue M γ π' s) := by sorry

end SuttonBartoRL.EpsSoft
