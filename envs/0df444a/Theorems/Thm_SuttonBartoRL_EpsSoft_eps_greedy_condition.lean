-- Prove2me | Theorems.Thm_SuttonBartoRL_EpsSoft_eps_greedy_condition
-- name    : SuttonBartoRL.EpsSoft.eps_greedy_condition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:00:26.157982+00:00
-- url     : https://prove2.me/theorems/8dbd8e11-3876-4351-83dc-d77e631b4b37
-- title:
--   Eq. (5.2): an ε-greedy policy satisfies the condition of the policy improvement theorem
-- statement:
--   Let a finite MDP be given with discount rate $0 \le \gamma < 1$, let $0 < \varepsilon \le 1$, let $\pi$ be an $\varepsilon$-soft policy and $\pi'$ an $\varepsilon$-greedy policy with respect to $q_\pi$. Then for every state $s$
--   $$
--   q_\pi(s, \pi'(s)) = \sum_a \pi'(a \mid s)\, q_\pi(s, a) = \frac{\varepsilon}{|\mathcal A|} \sum_a q_\pi(s, a) + (1 - \varepsilon) \max_a q_\pi(s, a),
--   $$
--   and
--   $$
--   q_\pi(s, \pi'(s)) \ge v_\pi(s).
--   $$
--
--   This is the condition (4.7) of the policy improvement theorem for the pair $\pi, \pi'$; it is what makes $\varepsilon$-greedy improvement work.
--
--   **Formalization Note** The book's chain divides by $1 - \varepsilon$ in an intermediate step; the statement here is the inequality between the two ends, which is meaningful for all $\varepsilon \in (0, 1]$ (at $\varepsilon = 1$ the only $\varepsilon$-soft policy is the uniform one, and equality holds). The maximum is over the finite nonempty action set.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (5.2) and the chain following it, pp. 101–102

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_EpsSoftPolicies

namespace SuttonBartoRL.EpsSoft

/-- Eq. (5.2), pp. 101–102: for a finite MDP with `0 ≤ γ < 1` and `0 < ε ≤ 1`, if `π` is `ε`-soft
and `π'` is `ε`-greedy with respect to `q_π`, then for every state `s`
`q_π(s, π'(s)) = Σ_a π'(a | s) q_π(s, a) = (ε / |A|) Σ_a q_π(s, a) + (1 - ε) max_a q_π(s, a)`,
and this is `≥ v_π(s)`: the condition (4.7) of the policy improvement theorem holds. -/
theorem eps_greedy_condition {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (π π' : SuttonBartoRL.FiniteMDP.Policy S A) (hπ : IsEpsSoft ε π) (hπ' : IsEpsGreedy M γ ε π π') :
    ∀ s, (∑ a, π'.prob s a * actionValue M γ π s a =
        ε / (Fintype.card A : ℝ) * ∑ a, actionValue M γ π s a +
          (1 - ε) * Finset.univ.sup' Finset.univ_nonempty (fun a => actionValue M γ π s a)) ∧
      stateValue M γ π s ≤ ∑ a, π'.prob s a * actionValue M γ π s a := by sorry

end SuttonBartoRL.EpsSoft
