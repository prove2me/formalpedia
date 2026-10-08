-- Prove2me | Theorems.Thm_SampleComplexityRL_ApproxDP_avi_rate
-- name    : SampleComplexityRL.ApproxDP.avi_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:11.373486+00:00
-- url     : https://prove2.me/theorems/dbc052c1-294e-4cc5-9546-5c9701202928
-- title:
--   p. 41, display after Theorem 3.2.1 — approximate value iteration rate: ‖V* − V_{π_t}‖∞ ≤ 2γ^t/(1−γ) + 2ε/(1−γ)²
-- statement:
--   In the setting of Theorem 3.2.1 (finite $\gamma$-discounted MDP, rewards in $[0,1]$, $0\le\gamma<1$, normalized values, optimal policy $\pi^*$, $V^*=V_{\pi^*}$), let $J_0=0,J_1,J_2,\dots$ satisfy $\|J_t-BJ_{t-1}\|_\infty\le\varepsilon$ for $t\ge1$, and let each $\pi_t$ be a deterministic policy greedy with respect to the lookahead of $J_t$:
--   $$\pi_t(s)\in\arg\max_a\big((1-\gamma)r(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[J_t(s')]\big).$$
--   Then for every $t\ge0$,
--   $$
--   \|V^*-V_{\pi_t}\|_\infty\le\frac{2\gamma^t}{1-\gamma}+\frac{2\varepsilon}{(1-\gamma)^2}.
--   $$
--
--   The rate $2\gamma^t/(1-\gamma)$ is worse than that of exact value iteration, $\|V^*-V_{\pi_t}\|_\infty\le2\gamma^t$.
--
--   **Formalization Note** $\|\cdot\|_\infty$ is the sup norm on `S → ℝ`; deterministic policies are evaluated as indicator policies; the approximation condition is written for indices $t+1$ and $t$.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 41, display following the proof of Theorem 3.2.1 (convergence rate of approximate value iteration)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_ApproxDP_Greedy
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared ApproxOptRL.PolicyQuality

namespace SampleComplexityRL.ApproxDP

/-- Kakade 2003, display after the proof of Theorem 3.2.1, p. 41. -/
theorem avi_rate
    {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (πstar : S → A → ℝ) (hopt : IsOptimalPolicy P r γ πstar)
    (ε : ℝ) (J : ℕ → S → ℝ) (π : ℕ → S → A)
    (hJ0 : J 0 = 0)
    (herr : ∀ t, ‖J (t + 1) - backup P r γ (J t)‖ ≤ ε)
    (hgreedy : ∀ t, IsGreedy (lookahead P r γ (J t)) (π t)) :
    ∀ t, ‖value P r γ πstar - value P r γ (detPolicy (π t))‖ ≤ 2 * γ ^ t / (1 - γ) + 2 * ε / (1 - γ) ^ 2 := by sorry

end SampleComplexityRL.ApproxDP
