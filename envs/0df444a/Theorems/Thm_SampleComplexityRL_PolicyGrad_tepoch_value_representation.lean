-- Prove2me | Theorems.Thm_SampleComplexityRL_PolicyGrad_tepoch_value_representation
-- name    : SampleComplexityRL.PolicyGrad.tepoch_value_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:29.772538+00:00
-- url     : https://prove2.me/theorems/501b0b34-de1f-405d-8945-315d7a5968e9
-- title:
--   p. 47 — T-epoch value as an expectation under the state-time distribution: V_π(s₀) = E_{(s,t)∼d_{π,s₀}} E_{a∼π(·|s,t)}[r(s,a)]
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set, $P(s'\mid s,a)$ a transition kernel, $r:S\times A\to[0,1]$ a reward function and $T\ge1$ a horizon. Let $\pi(a\mid s,t)$ be a non-stationary policy (a probability distribution on $A$ for each state $s$ and epoch $t<T$) and $s_0\in S$ a start state. Write $V_\pi(s_0)$ for the normalized $T$-epoch value and $d_{\pi,s_0}(s,t)=\frac1T\Pr(s_t=s\mid\pi,s_0)$ for the future state-time distribution on $S\times\{0,\dots,T-1\}$. Then
--   $$
--   V_\pi(s_0)=\mathbb E_{(s,t)\sim d_{\pi,s_0}}\,\mathbb E_{a\sim\pi(\cdot\mid s,t)}\big[r(s,a)\big]=\sum_{s\in S}\sum_{t=0}^{T-1}d_{\pi,s_0}(s,t)\sum_{a\in A}\pi(a\mid s,t)\,r(s,a).
--   $$
--
--   The identity says that the normalized value is the average reward under the distribution of state-time pairs visited by $\pi$, which is the motivation for the future distributions used throughout the thesis.
--
--   **Formalization Note** Expectations over the finite sets are finite sums; epochs are 0-based.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 47, display after Definition 4.2.2 (T-epoch case)

import Mathlib
import Definitions.Def_SampleComplexityRL_PolicyGrad_TEpoch

namespace SampleComplexityRL.PolicyGrad

open FoundationsML.ReinforcementLearning

/-- Kakade 2003, p. 47 (display after Definition 4.2.2): for a `T`-epoch MDP,
`V_π(s₀) = E_{(s,t) ∼ d_{π,s₀}} E_{a ∼ π(·|s,t)}[r(s,a)]`. -/
theorem tepoch_value_representation {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : NSPolicy S A) (s₀ : S)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hT : 0 < T) (hπ : IsNSPolicy T π) :
    value P r T π s₀ =
      ∑ s, ∑ t ∈ Finset.range T, stateTimeDist P π s₀ T s t *
        ∑ a, π t s a * r s a := by sorry

end SampleComplexityRL.PolicyGrad
