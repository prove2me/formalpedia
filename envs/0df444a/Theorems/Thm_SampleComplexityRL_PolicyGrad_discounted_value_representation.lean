-- Prove2me | Theorems.Thm_SampleComplexityRL_PolicyGrad_discounted_value_representation
-- name    : SampleComplexityRL.PolicyGrad.discounted_value_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:08.298407+00:00
-- url     : https://prove2.me/theorems/9b22892f-6e1f-4b9a-9a38-35e0b031f14c
-- title:
--   p. 47 — discounted value as an expectation under the future state distribution: V_{π,γ}(s₀) = E_{s∼d_{π,s₀,γ}} E_{a∼π(·|s)}[r(s,a)]
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set, $P(s'\mid s,a)$ a transition kernel, $r:S\times A\to[0,1]$ a reward function and $0\le\gamma<1$ a discount factor. Let $\pi(a\mid s)$ be a stationary stochastic policy and $s_0\in S$. Write
--   $$V_{\pi,\gamma}(s_0)=(1-\gamma)\,\mathbb E\Big[\sum_{\tau=0}^\infty\gamma^\tau r(s_\tau,a_\tau)\,\Big|\,\pi,s_0\Big]$$
--   for the normalized discounted value and $d_{\pi,s_0,\gamma}(s)=(1-\gamma)\sum_{t=0}^\infty\gamma^t\Pr(s_t=s\mid\pi,s_0)$ for the $\gamma$-discounted future state distribution. Then
--   $$
--   V_{\pi,\gamma}(s_0)=\mathbb E_{s\sim d_{\pi,s_0,\gamma}}\,\mathbb E_{a\sim\pi(\cdot\mid s)}\big[r(s,a)\big]=\sum_{s\in S}d_{\pi,s_0,\gamma}(s)\sum_{a\in A}\pi(a\mid s)\,r(s,a).
--   $$
--
--   This is the discounted counterpart of the $T$-epoch representation: the normalized value is the average one-step reward under the discounted distribution of visited states.
--
--   **Formalization Note** The value and $d_{\pi,s_0,\gamma}$ are those of the published normalized model `ApproxOptRL.Shared.Model`; $d_{\pi,s_0,\gamma}$ is its `futureStateDist` at the point mass on $s_0$. Both are infinite series (`tsum`), which converge because $\gamma<1$ and the summands are bounded.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 47, display after Definition 4.2.2 (infinite horizon case)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model

namespace SampleComplexityRL.PolicyGrad

open FoundationsML.ReinforcementLearning ApproxOptRL.Shared

/-- Kakade 2003, p. 47 (display after Definition 4.2.2): for a stationary policy `π`,
`V_{π,γ}(s₀) = E_{s ∼ d_{π,s₀,γ}} E_{a ∼ π(·|s)}[r(s,a)]`. -/
theorem discounted_value_representation {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A → ℝ) (s₀ : S)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hπ : IsPolicy π) :
    ApproxOptRL.Shared.value P r γ π s₀ =
      ∑ s, futureStateDist P γ π (fun s' => if s' = s₀ then 1 else 0) s *
        ∑ a, π s a * r s a := by sorry

end SampleComplexityRL.PolicyGrad
