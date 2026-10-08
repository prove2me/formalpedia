-- Prove2me | Theorems.Thm_SampleComplexityRL_ApproxDP_greedy_loss_bound
-- name    : SampleComplexityRL.ApproxDP.greedy_loss_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:04.964439+00:00
-- url     : https://prove2.me/theorems/d0c408f3-cda6-4d29-ac36-f74ec4b3352d
-- title:
--   Theorem 3.1.1 — a policy greedy for an ε-accurate Q* loses at most 2ε/(1−γ)
-- statement:
--   Consider a finite $\gamma$-discounted MDP with state set $S$, nonempty action set $A$, transition kernel $P$, rewards $r(s,a)\in[0,1]$ and $0\le\gamma<1$, with **normalized** values $V_\pi(s)=(1-\gamma)\,\mathbb E\big[\sum_{t\ge0}\gamma^t r(s_t,a_t)\mid\pi,s_0=s\big]$ and $Q_\pi(s,a)=(1-\gamma)r(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[V_\pi(s')]$. Let $\pi^*$ be an optimal policy, $V^*=V_{\pi^*}$ and $Q^*=Q_{\pi^*}$.
--
--   Let $\tilde Q\in\mathbb R^{S\times A}$ satisfy $\|\tilde Q-Q^*\|_\infty\le\varepsilon$, where $\|x\|_\infty=\max_{s,a}|x(s,a)|$, and let $\pi$ be a deterministic policy greedy with respect to $\tilde Q$, i.e. $\pi(s)\in\arg\max_a\tilde Q(s,a)$ for every $s$. Then for all states $s$,
--   $$
--   V_\pi(s)\ge V^*(s)-\frac{2\varepsilon}{1-\gamma}.
--   $$
--
--   The result bounds the loss caused by acting greedily with respect to an approximation of $Q^*$; it is the step that converts value-function accuracy into policy quality in both approximate value iteration and approximate policy iteration.
--
--   **Formalization Note** The optimal policy is a stationary stochastic policy whose normalized value dominates that of every stationary stochastic policy at every state (`IsOptimalPolicy`); for a finite MDP this is the thesis's optimal policy, and such a policy exists (thesis, p. 26). The deterministic policy $\pi$ is evaluated as the indicator policy. The greedy condition holds for every tie-breaking rule.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 39, Theorem 3.1.1 (setting p. 38, Section 3.1)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_ApproxDP_Greedy
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared ApproxOptRL.PolicyQuality

namespace SampleComplexityRL.ApproxDP

/-- Kakade 2003, Theorem 3.1.1, p. 39. -/
theorem greedy_loss_bound
    {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (πstar : S → A → ℝ) (hopt : IsOptimalPolicy P r γ πstar)
    (ε : ℝ) (Qtil : S → A → ℝ) (f : S → A)
    (hQ : ‖Qtil - qValue P r γ πstar‖ ≤ ε) (hf : IsGreedy Qtil f) :
    ∀ s, value P r γ πstar s - 2 * ε / (1 - γ) ≤ value P r γ (detPolicy f) s := by sorry

end SampleComplexityRL.ApproxDP
