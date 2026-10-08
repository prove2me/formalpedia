-- Prove2me | Theorems.Thm_SuttonBartoRL_EpsSoft_unimproved_fixed_point
-- name    : SuttonBartoRL.EpsSoft.unimproved_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:00:41.283541+00:00
-- url     : https://prove2.me/theorems/4221352e-176c-4db7-979d-91cbe0e491ec
-- title:
--   p. 102: the value of an ε-soft policy that is no longer improved satisfies the altered optimality equation
-- statement:
--   Let a finite MDP be given with discount rate $0 \le \gamma < 1$, let $0 < \varepsilon \le 1$, let $\pi$ be $\varepsilon$-soft and $\pi'$ $\varepsilon$-greedy with respect to $q_\pi$, and suppose $v_{\pi'} = v_\pi$ (the policy is no longer improved). Then for every state $s$
--   $$
--   v_\pi(s) = (1 - \varepsilon) \max_a q_\pi(s, a) + \frac{\varepsilon}{|\mathcal A|} \sum_a q_\pi(s, a)
--   $$
--   $$
--   = (1 - \varepsilon) \max_a \sum_{s', r} p(s', r \mid s, a)\big[r + \gamma v_\pi(s')\big] + \frac{\varepsilon}{|\mathcal A|} \sum_a \sum_{s', r} p(s', r \mid s, a)\big[r + \gamma v_\pi(s')\big].
--   $$
--
--   This is the same equation as the one for $\tilde v_*$ with $v_\pi$ substituted; by uniqueness, an unimproved $\varepsilon$-soft policy has $v_\pi = \tilde v_*$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.4, p. 102 ('When equality holds and the ε-soft policy π is no longer improved, then we also know, from (5.2), that …')

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_EpsSoftPolicies

namespace SuttonBartoRL.EpsSoft

/-- p. 102: for a finite MDP with `0 ≤ γ < 1` and `0 < ε ≤ 1`, if `π` is `ε`-soft, `π'` is
`ε`-greedy with respect to `q_π`, and `v_{π'} = v_π` (the policy is no longer improved), then for
every state `s`
`v_π(s) = (1 - ε) max_a q_π(s, a) + (ε / |A|) Σ_a q_π(s, a)
        = (1 - ε) max_a Σ_{s', r} p(s', r | s, a) [r + γ v_π(s')] + (ε / |A|) Σ_a Σ_{s', r} p(s', r | s, a) [r + γ v_π(s')]`. -/
theorem unimproved_fixed_point {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (π π' : SuttonBartoRL.FiniteMDP.Policy S A) (hπ : IsEpsSoft ε π)
    (hπ' : IsEpsGreedy M γ ε π π') (heq : ∀ s, stateValue M γ π' s = stateValue M γ π s) :
    ∀ s, (stateValue M γ π s =
        (1 - ε) * Finset.univ.sup' Finset.univ_nonempty (fun a => actionValue M γ π s a) +
          ε / (Fintype.card A : ℝ) * ∑ a, actionValue M γ π s a) ∧
      stateValue M γ π s =
        (1 - ε) * Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ s', ∑ r ∈ M.R,
          M.p s a s' r * (r + γ * stateValue M γ π s')) +
        ε / (Fintype.card A : ℝ) * ∑ a, ∑ s', ∑ r ∈ M.R,
          M.p s a s' r * (r + γ * stateValue M γ π s') := by sorry

end SuttonBartoRL.EpsSoft
