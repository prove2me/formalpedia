-- Prove2me | Theorems.Thm_SampleComplexityRL_ApproxDP_api_one_step
-- name    : SampleComplexityRL.ApproxDP.api_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:13.763908+00:00
-- url     : https://prove2.me/theorems/8f93540e-3d17-4429-81e7-588c266b3fef
-- title:
--   Lemma 3.2.3 — one step of approximate policy iteration: ‖V* − V_{π_{t+1}}‖∞ ≤ γ‖V* − V_{π_t}‖∞ + 2ε/(1−γ)
-- statement:
--   Consider a finite $\gamma$-discounted MDP ($S$, nonempty $A$, kernel $P$, rewards $r(s,a)\in[0,1]$, $0\le\gamma<1$) with normalized values $V_\pi$ and state-action values $Q_\pi(s,a)=(1-\gamma)r(s,a)+\gamma\,\mathbb E_{s'}[V_\pi(s')]$, and an optimal policy $\pi^*$ with $V^*=V_{\pi^*}$.
--
--   **$\gamma$-approximate policy iteration** produces deterministic policies $\pi_0,\pi_1,\dots$ and approximations $\tilde Q_0,\tilde Q_1,\dots$ as follows: $\pi_0$ is arbitrary; $\tilde Q_t$ approximates $Q_{\pi_t}$; and $\pi_{t+1}$ is greedy with respect to $\tilde Q_t$, i.e. $\pi_{t+1}(s)\in\arg\max_a\tilde Q_t(s,a)$. Assume that for every $t$
--   $$\|\tilde Q_t-Q_{\pi_t}\|_\infty\le\varepsilon,$$
--   with $\|x\|_\infty=\max_{s,a}|x(s,a)|$. Then for every $t$,
--   $$
--   \|V^*-V_{\pi_{t+1}}\|_\infty\le\gamma\,\|V^*-V_{\pi_t}\|_\infty+\frac{2\varepsilon}{1-\gamma},
--   $$
--   where on state vectors $\|x\|_\infty=\max_s|x(s)|$.
--
--   The lemma is a pseudo-contraction: improvement at each step is not guaranteed, but the distance to optimality contracts up to an additive error. Theorem 3.2.2 and the convergence rate of approximate policy iteration follow from it.
--
--   **Formalization Note** The run is given by the sequences $\pi_t$ and $\tilde Q_t$ together with the greedy relation $\pi_{t+1}$ greedy for $\tilde Q_t$ (every tie-breaking) and the accuracy hypothesis at every $t$. Deterministic policies are evaluated as indicator policies.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 41, Lemma 3.2.3 (algorithm: Section 3.2.2, p. 41)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_ApproxDP_Greedy
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared ApproxOptRL.PolicyQuality

namespace SampleComplexityRL.ApproxDP

/-- Kakade 2003, Lemma 3.2.3, p. 41. -/
theorem api_one_step
    {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (πstar : S → A → ℝ) (hopt : IsOptimalPolicy P r γ πstar)
    (ε : ℝ) (π : ℕ → S → A) (Qt : ℕ → S → A → ℝ)
    (hgreedy : ∀ t, IsGreedy (Qt t) (π (t + 1)))
    (herr : ∀ t, ‖Qt t - qValue P r γ (detPolicy (π t))‖ ≤ ε) :
    ∀ t, ‖value P r γ πstar - value P r γ (detPolicy (π (t + 1)))‖
      ≤ γ * ‖value P r γ πstar - value P r γ (detPolicy (π t))‖ + 2 * ε / (1 - γ) := by sorry

end SampleComplexityRL.ApproxDP
