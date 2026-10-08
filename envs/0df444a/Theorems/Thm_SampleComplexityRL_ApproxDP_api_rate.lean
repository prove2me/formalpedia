-- Prove2me | Theorems.Thm_SampleComplexityRL_ApproxDP_api_rate
-- name    : SampleComplexityRL.ApproxDP.api_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:10.302403+00:00
-- url     : https://prove2.me/theorems/c4944cc8-90ab-4839-bf81-68a307ec2595
-- title:
--   p. 41, display after Lemma 3.2.3 — approximate policy iteration rate: ‖V* − V_{π_t}‖∞ ≤ γ^t + 2ε/(1−γ)²
-- statement:
--   In the setting of Lemma 3.2.3 (finite $\gamma$-discounted MDP with rewards in $[0,1]$, $0\le\gamma<1$, normalized values, optimal policy $\pi^*$, $V^*=V_{\pi^*}$), let $\pi_0,\pi_1,\dots$ and $\tilde Q_0,\tilde Q_1,\dots$ be a run of $\gamma$-approximate policy iteration: $\pi_0$ is an arbitrary deterministic policy, $\pi_{t+1}$ is greedy with respect to $\tilde Q_t$, and $\|\tilde Q_t-Q_{\pi_t}\|_\infty\le\varepsilon$ for every $t$. Then for every $t\ge0$,
--   $$
--   \|V^*-V_{\pi_t}\|_\infty\le\gamma^t+\frac{2\varepsilon}{(1-\gamma)^2}.
--   $$
--
--   The rate matches that of exact policy iteration, $\|V^*-V_{\pi_t}\|_\infty\le\gamma^t$, up to the additive limit term.
--
--   **Formalization Note** The leading term $\gamma^t$ (rather than $\gamma^t\|V^*-V_{\pi_0}\|_\infty$) uses that normalized values of rewards in $[0,1]$ lie in $[0,1]$, so that $\|V^*-V_{\pi_0}\|_\infty\le1$; the reward bound is therefore a needed hypothesis.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 41, display after Lemma 3.2.3 (convergence rate of approximate policy iteration)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_ApproxDP_Greedy
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared ApproxOptRL.PolicyQuality

namespace SampleComplexityRL.ApproxDP

/-- Kakade 2003, display after Lemma 3.2.3, p. 41. -/
theorem api_rate
    {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (πstar : S → A → ℝ) (hopt : IsOptimalPolicy P r γ πstar)
    (ε : ℝ) (π : ℕ → S → A) (Qt : ℕ → S → A → ℝ)
    (hgreedy : ∀ t, IsGreedy (Qt t) (π (t + 1)))
    (herr : ∀ t, ‖Qt t - qValue P r γ (detPolicy (π t))‖ ≤ ε) :
    ∀ t, ‖value P r γ πstar - value P r γ (detPolicy (π t))‖ ≤ γ ^ t + 2 * ε / (1 - γ) ^ 2 := by sorry

end SampleComplexityRL.ApproxDP
