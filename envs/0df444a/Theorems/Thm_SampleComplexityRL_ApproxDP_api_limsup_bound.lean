-- Prove2me | Theorems.Thm_SampleComplexityRL_ApproxDP_api_limsup_bound
-- name    : SampleComplexityRL.ApproxDP.api_limsup_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:20.74035+00:00
-- url     : https://prove2.me/theorems/94357a04-44b6-4ea3-a551-bc2d3bfb1c31
-- title:
--   Theorem 3.2.2 — approximate policy iteration: lim sup ‖V* − V_{π_t}‖∞ ≤ 2ε/(1−γ)²
-- statement:
--   Consider a finite $\gamma$-discounted MDP: finite state set $S$, finite nonempty action set $A$, transition kernel $P(s'\mid s,a)$, deterministic rewards $r(s,a)\in[0,1]$ and $0\le\gamma<1$. Values are **normalized**: $V_\pi(s)=(1-\gamma)\,\mathbb E\big[\sum_{t\ge0}\gamma^t r(s_t,a_t)\mid\pi,s_0=s\big]$ and $Q_\pi(s,a)=(1-\gamma)r(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[V_\pi(s')]$. Let $\pi^*$ be an optimal policy and $V^*=V_{\pi^*}$.
--
--   **$\gamma$-approximate policy iteration** produces deterministic policies $\pi_0,\pi_1,\dots$ and approximations $\tilde Q_0,\tilde Q_1,\dots$: $\pi_0$ is arbitrary, $\tilde Q_t$ approximates $Q_{\pi_t}$, and $\pi_{t+1}$ is greedy with respect to $\tilde Q_t$, i.e. $\pi_{t+1}(s)\in\arg\max_a\tilde Q_t(s,a)$. Assume
--   $$\|\tilde Q_t-Q_{\pi_t}\|_\infty\le\varepsilon\quad\text{for every }t,$$
--   with $\|x\|_\infty=\max_{s,a}|x(s,a)|$. Then
--   $$
--   \limsup_{t\to\infty}\|V^*-V_{\pi_t}\|_\infty\le\frac{2\varepsilon}{(1-\gamma)^2},
--   $$
--   with $\|x\|_\infty=\max_s|x(s)|$ on state vectors.
--
--   The policies need not converge, but the values of the policies visited eventually lie within $2\varepsilon/(1-\gamma)^2$ of optimal in max norm. The bound is stated in terms of the worst-case (max-norm) evaluation error, which the thesis argues is the appropriate error for greedy schemes.
--
--   **Formalization Note** The lim sup is stated in $\varepsilon$–$N$ form: for every $\delta>0$ there is $N$ such that $\|V^*-V_{\pi_t}\|_\infty\le 2\varepsilon/(1-\gamma)^2+\delta$ for all $t\ge N$; this is equivalent to the lim sup bound for the bounded sequence at hand and avoids Mathlib's junk value of `limsup` on unbounded sequences. Deterministic policies are evaluated as indicator policies; the greedy relation allows every tie-breaking rule; the optimal policy is a stationary policy dominating every stationary stochastic policy at every state.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 41, Theorem 3.2.2 (algorithm: Section 3.2.2, p. 41)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_ApproxDP_Greedy
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared ApproxOptRL.PolicyQuality

namespace SampleComplexityRL.ApproxDP

/-- Kakade 2003, Theorem 3.2.2, p. 41 (limsup in ε–N form). -/
theorem api_limsup_bound
    {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (πstar : S → A → ℝ) (hopt : IsOptimalPolicy P r γ πstar)
    (ε : ℝ) (π : ℕ → S → A) (Qt : ℕ → S → A → ℝ)
    (hgreedy : ∀ t, IsGreedy (Qt t) (π (t + 1)))
    (herr : ∀ t, ‖Qt t - qValue P r γ (detPolicy (π t))‖ ≤ ε) :
    ∀ δ > 0, ∃ N : ℕ, ∀ t ≥ N, ‖value P r γ πstar - value P r γ (detPolicy (π t))‖ ≤ 2 * ε / (1 - γ) ^ 2 + δ := by sorry

end SampleComplexityRL.ApproxDP
