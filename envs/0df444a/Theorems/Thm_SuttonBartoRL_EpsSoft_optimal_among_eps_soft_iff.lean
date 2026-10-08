-- Prove2me | Theorems.Thm_SuttonBartoRL_EpsSoft_optimal_among_eps_soft_iff
-- name    : SuttonBartoRL.EpsSoft.optimal_among_eps_soft_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:00:08.684408+00:00
-- url     : https://prove2.me/theorems/a6607a92-1327-4c99-95ef-23f3621ea281
-- title:
--   p. 102: π is optimal among ε-soft policies if and only if v_π = ṽ_*
-- statement:
--   Let a finite MDP be given with discount rate $0 \le \gamma < 1$ and let $0 < \varepsilon \le 1$. Let $\tilde v_*$ be the optimal state-value function of the new environment, in which with probability $\varepsilon$ the chosen action is replaced by a uniformly random one. Then an $\varepsilon$-soft policy $\pi$ is optimal among the $\varepsilon$-soft policies if and only if
--   $$
--   v_\pi(s) = \tilde v_*(s) \qquad \text{for all } s \in \mathcal S,
--   $$
--   where $v_\pi$ is the value of $\pi$ in the original MDP.
--
--   Together with the uniqueness of $\tilde v_*$ as the solution of the altered Bellman optimality equation, this reduces optimality among $\varepsilon$-soft policies to a fixed-point equation.
--
--   **Formalization Note** "$\pi$ is optimal among $\varepsilon$-soft policies" means $\pi$ is $\varepsilon$-soft and $v_{\pi''} \le v_\pi$ pointwise for every $\varepsilon$-soft $\pi''$. The equivalence is stated for $\varepsilon$-soft $\pi$, as the book's sentence is about such policies.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.4, p. 102 ('Then a policy π is optimal among ε-soft policies if and only if v_π = ṽ_*')

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_EpsSoftPolicies
import Definitions.Def_SuttonBartoRL_EpsSoft_NewEnvironment

namespace SuttonBartoRL.EpsSoft

/-- p. 102: let `ṽ_*` be the optimal state-value function of the new environment `epsEnv M ε`
(the `ε`-softness moved inside the environment). For a finite MDP with `0 ≤ γ < 1` and
`0 < ε ≤ 1`, an `ε`-soft policy `π` is optimal among the `ε`-soft policies if and only if
`v_π = ṽ_*`, where `v_π` is its value in the original MDP. -/
theorem optimal_among_eps_soft_iff {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (π : SuttonBartoRL.FiniteMDP.Policy S A) (hπ : IsEpsSoft ε π) :
    IsOptimalAmongEpsSoft M γ ε π ↔
      ∀ s, stateValue M γ π s = optimalValue (epsEnv M ε hε0.le hε1) γ s := by sorry

end SuttonBartoRL.EpsSoft
