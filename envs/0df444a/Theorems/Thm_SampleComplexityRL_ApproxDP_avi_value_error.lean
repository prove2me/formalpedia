-- Prove2me | Theorems.Thm_SampleComplexityRL_ApproxDP_avi_value_error
-- name    : SampleComplexityRL.ApproxDP.avi_value_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:17.994826+00:00
-- url     : https://prove2.me/theorems/6c45c984-45da-4b86-8fa5-f12f8dad43d4
-- title:
--   p. 40, display in the proof of Theorem 3.2.1 — approximate value iteration: ‖V* − J_t‖∞ ≤ γ^t + ε/(1−γ)
-- statement:
--   Consider a finite $\gamma$-discounted MDP ($S$, nonempty $A$, kernel $P$, rewards $r(s,a)\in[0,1]$, $0\le\gamma<1$) with normalized values, an optimal policy $\pi^*$ and $V^*=V_{\pi^*}$. Let $B$ be the backup operator $[BJ](s)=\max_a\big((1-\gamma)r(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[J(s')]\big)$.
--
--   **$\gamma$-approximate value iteration** produces vectors $J_0,J_1,\dots\in\mathbb R^S$ with $J_0=0$ and
--   $$\|J_t-BJ_{t-1}\|_\infty\le\varepsilon\qquad(t\ge1),$$
--   where $\|x\|_\infty=\max_s|x(s)|$, together with greedy policies $\pi_t(s)\in\arg\max_a\big((1-\gamma)r(s,a)+\gamma\,\mathbb E_{s'}[J_t(s')]\big)$. Then for every $t\ge0$,
--   $$
--   \|V^*-J_t\|_\infty\le\gamma^t+\frac{\varepsilon}{1-\gamma}.
--   $$
--
--   This is the estimate on the iterates themselves from which Theorem 3.2.1 and the convergence rate of approximate value iteration are derived.
--
--   **Formalization Note** The approximation condition is written for consecutive indices $t+1$ and $t$ ($t\ge0$), avoiding natural-number subtraction. The term $\gamma^t$ uses $J_0=0$ and $\|V^*\|_\infty\le1$, which holds because rewards lie in $[0,1]$ and values are normalized. The greedy policies are part of the run's data but do not enter this conclusion.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 40, display in the proof of Theorem 3.2.1 (algorithm: Section 3.2.1, p. 40)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_ApproxDP_Greedy
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared ApproxOptRL.PolicyQuality

namespace SampleComplexityRL.ApproxDP

/-- Kakade 2003, display in the proof of Theorem 3.2.1, p. 40. -/
theorem avi_value_error
    {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (πstar : S → A → ℝ) (hopt : IsOptimalPolicy P r γ πstar)
    (ε : ℝ) (J : ℕ → S → ℝ) (π : ℕ → S → A)
    (hJ0 : J 0 = 0)
    (herr : ∀ t, ‖J (t + 1) - backup P r γ (J t)‖ ≤ ε)
    (hgreedy : ∀ t, IsGreedy (lookahead P r γ (J t)) (π t)) :
    ∀ t, ‖value P r γ πstar - J t‖ ≤ γ ^ t + ε / (1 - γ) := by sorry

end SampleComplexityRL.ApproxDP
