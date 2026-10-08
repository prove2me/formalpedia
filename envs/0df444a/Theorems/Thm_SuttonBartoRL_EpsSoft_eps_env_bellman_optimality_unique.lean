-- Prove2me | Theorems.Thm_SuttonBartoRL_EpsSoft_eps_env_bellman_optimality_unique
-- name    : SuttonBartoRL.EpsSoft.eps_env_bellman_optimality_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:39:05.557985+00:00
-- url     : https://prove2.me/theorems/9e32f627-5bea-4c6f-829c-5761f668cedd
-- title:
--   p. 102: ṽ_* is the unique solution of the Bellman optimality equation with altered transition probabilities
-- statement:
--   Let a finite MDP be given with discount rate $0 \le \gamma < 1$ and let $0 < \varepsilon \le 1$. Let $\tilde v_*$ be the optimal state-value function of the new environment with dynamics $\tilde p(s', r \mid s, a) = (1-\varepsilon) p(s', r \mid s, a) + \sum_{a'} \frac{\varepsilon}{|\mathcal A|} p(s', r \mid s, a')$. Then for every state $s$
--   $$
--   \tilde v_*(s) = \max_a \sum_{s', r} \Big[(1 - \varepsilon)\, p(s', r \mid s, a) + \sum_{a'} \frac{\varepsilon}{|\mathcal A|}\, p(s', r \mid s, a')\Big]\big[r + \gamma \tilde v_*(s')\big]
--   $$
--   $$
--   = (1 - \varepsilon) \max_a \sum_{s', r} p(s', r \mid s, a)\big[r + \gamma \tilde v_*(s')\big] + \frac{\varepsilon}{|\mathcal A|} \sum_a \sum_{s', r} p(s', r \mid s, a)\big[r + \gamma \tilde v_*(s')\big],
--   $$
--   and $\tilde v_*$ is the only function $w : \mathcal S \to \mathbb R$ satisfying the first equation with $w$ in place of $\tilde v_*$.
--
--   This is the Bellman optimality equation (3.19) of the new environment; its uniqueness is what identifies the value of an unimproved $\varepsilon$-soft policy with $\tilde v_*$.
--
--   **Formalization Note** $\tilde v_*$ is the supremum of the new environment's policy values over all stochastic policies; for $0 \le \gamma < 1$ this family is bounded.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.4, p. 102 (displayed equation for ṽ_*, 'the unique solution to the Bellman optimality equation (3.19) with altered transition probabilities')

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_ValueFunctions
import Definitions.Def_SuttonBartoRL_EpsSoft_NewEnvironment

namespace SuttonBartoRL.EpsSoft

/-- p. 102: for a finite MDP with `0 ≤ γ < 1` and `0 < ε ≤ 1`, the optimal state-value function
`ṽ_*` of the new environment `epsEnv M ε` is the unique solution of the Bellman optimality
equation (3.19) with altered transition probabilities
`ṽ_*(s) = max_a Σ_{s', r} [(1 - ε) p(s', r | s, a) + Σ_{a'} (ε / |A|) p(s', r | s, a')] [r + γ ṽ_*(s')]`,
and the right-hand side equals
`(1 - ε) max_a Σ_{s', r} p(s', r | s, a) [r + γ ṽ_*(s')] + (ε / |A|) Σ_a Σ_{s', r} p(s', r | s, a) [r + γ ṽ_*(s')]`. -/
theorem eps_env_bellman_optimality_unique {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    (∀ s, optimalValue (epsEnv M ε hε0.le hε1) γ s =
        Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ s', ∑ r ∈ M.R,
          ((1 - ε) * M.p s a s' r + ∑ a', ε / (Fintype.card A : ℝ) * M.p s a' s' r) *
            (r + γ * optimalValue (epsEnv M ε hε0.le hε1) γ s'))) ∧
    (∀ s, optimalValue (epsEnv M ε hε0.le hε1) γ s =
        (1 - ε) * Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ s', ∑ r ∈ M.R,
          M.p s a s' r * (r + γ * optimalValue (epsEnv M ε hε0.le hε1) γ s')) +
        ε / (Fintype.card A : ℝ) * ∑ a, ∑ s', ∑ r ∈ M.R,
          M.p s a s' r * (r + γ * optimalValue (epsEnv M ε hε0.le hε1) γ s')) ∧
    (∀ w : S → ℝ, (∀ s, w s =
        Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ s', ∑ r ∈ M.R,
          ((1 - ε) * M.p s a s' r + ∑ a', ε / (Fintype.card A : ℝ) * M.p s a' s' r) *
            (r + γ * w s'))) →
      w = optimalValue (epsEnv M ε hε0.le hε1) γ) := by sorry

end SuttonBartoRL.EpsSoft
