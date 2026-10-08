-- Prove2me | Theorems.Thm_SuttonBartoRL_DP_policy_improvement_theorem_stochastic
-- name    : SuttonBartoRL.DP.policy_improvement_theorem_stochastic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:51:07.129379+00:00
-- url     : https://prove2.me/theorems/ec41f016-dc48-4ee8-ba60-cbf3fb88cf41
-- title:
--   Policy improvement theorem for stochastic policies
-- statement:
--   Let $\pi$ and $\pi'$ be stochastic policies of a finite MDP with discount $0 \le \gamma < 1$, and write
--   $$
--   q_\pi(s, \pi'(s)) \;=\; \sum_a \pi'(a\mid s)\, q_\pi(s,a).
--   $$
--   If $q_\pi(s, \pi'(s)) \ge v_\pi(s)$ for all $s \in \mathcal S$, then
--   $$
--   v_{\pi'}(s) \;\ge\; v_\pi(s) \qquad \text{for all } s \in \mathcal S,
--   $$
--   and at every state $s$ where $q_\pi(s, \pi'(s)) > v_\pi(s)$, also $v_{\pi'}(s) > v_\pi(s)$.
--
--   This is the form of the theorem used for $\varepsilon$-greedy improvement in Chapter 5 and for stochastic greedy policies that split probability among tied actions.
--
--   **Formalization Note** The book asserts only that the theorem "carries through as stated for the stochastic case" (p. 79). The reading of $q_\pi(s,\pi'(s))$ as the $\pi'$-average of $q_\pi(s,\cdot)$ is the one the book itself uses in (5.2), p. 101.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §4.2, p. 79 ("carries through as stated for the stochastic case"); reading of q_π(s, π′(s)) from (5.2), p. 101

import Mathlib
import Definitions.Def_SuttonBartoRL_DP_MDP
import Definitions.Def_SuttonBartoRL_DP_ValueFunctions

namespace SuttonBartoRL.DP

/-- Policy improvement theorem for stochastic policies, Sutton & Barto (2018), p. 79 ("carries
through as stated for the stochastic case"), with `q_π(s, π'(s)) = Σ_a π'(a | s) q_π(s, a)` as in
(5.2), p. 101: if `Σ_a π'(a | s) q_π(s, a) ≥ v_π(s)` for all `s`, then `v_{π'}(s) ≥ v_π(s)` for all
`s`, strictly at every state where the hypothesis is strict. -/
theorem policy_improvement_theorem_stochastic {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π π' : Policy S A)
    (h47 : ∀ s, stateValue M γ π s ≤ ∑ a, π'.prob s a * actionValue M γ π s a) :
    (∀ s, stateValue M γ π s ≤ stateValue M γ π' s) ∧
    (∀ s, stateValue M γ π s < ∑ a, π'.prob s a * actionValue M γ π s a →
      stateValue M γ π s < stateValue M γ π' s) := by sorry

end SuttonBartoRL.DP
