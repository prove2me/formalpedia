-- Prove2me | Theorems.Thm_SampleComplexityRL_Mismeasure_greedy_bellman_error_bound
-- name    : SampleComplexityRL.Mismeasure.greedy_bellman_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:06.715314+00:00
-- url     : https://prove2.me/theorems/fe43afad-7dd9-4d71-85f9-b811b694073f
-- title:
--   Theorem 5.1.3 (Williams–Baird) — a greedy policy for J satisfies V_{π,γ}(s) ≥ V*_γ(s) − 2B_J/(1−γ)
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set, $P$ a transition kernel, $r:S\times A\to[0,1]$ a reward function and $0\le\gamma<1$. Let $J\in\mathbb R^S$ be a vector on the state space, $Q_J(s,a)=(1-\gamma)r(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[J(s')]$, and $B_J=\sup_{s,a}|Q_J(s,a)-J(s)|$ its Bellman error. Let $\pi$ be a greedy (deterministic stationary) policy with respect to $J$, i.e. $\pi(s)\in\arg\max_aQ_J(s,a)$ for every $s$, and let $V^*_\gamma$ be the optimal normalized discounted value. Then for all states $s$,
--   $$V_{\pi,\gamma}(s)\;\ge\;V^*_\gamma(s)-\frac{2B_J}{1-\gamma}.$$
--
--   This restates the Williams–Baird error bound in the normalized setting: a small Bellman error certifies a near-optimal greedy policy, at the price of a max-norm error measure.
--
--   **Formalization Note** $B_J$ is the number printed in Definition 5.1.2, a supremum over all state-action pairs (formalized as the sup norm on `S → A → ℝ`); it is at least the classical residual $\max_s|\max_aQ_J(s,a)-J(s)|$, so this statement is the thesis's (weaker) form of the Williams–Baird bound. $V^*_\gamma$ is the value of an optimal stationary policy (`IsOptimalPolicy`). Greediness is the relation $Q_J(s,a)\le Q_J(s,\pi(s))$, any tie-breaking.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 59, Theorem 5.1.3 (Definition 5.1.2, p. 58)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_Mismeasure_BellmanError
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared ApproxOptRL.PolicyQuality

namespace SampleComplexityRL.Mismeasure

/-- **Theorem 5.1.3** (Williams and Baird 1993; Kakade 2003, p. 59). In the normalized discounted
model (finite `S`, `A`, transition kernel `P`, rewards in `[0,1]`, `0 ≤ γ < 1`), let `J` be a
vector on the state space with Bellman error `B_J = sup_{s,a} |Q_J(s,a) - J(s)|`
(Definition 5.1.2), and let `f` be a greedy policy with respect to `J`
(`Q_J(s,a) ≤ Q_J(s,f(s))` for all `s`, `a`). With `πstar` an optimal stationary policy
(`V*_γ = V_{πstar,γ}`), for all states `s`: `V_{f,γ}(s) ≥ V*_γ(s) - 2 B_J / (1-γ)`. -/
theorem greedy_bellman_error_bound {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (πstar : S → A → ℝ) (hstar : IsOptimalPolicy P r γ πstar)
    (J : S → ℝ) (f : S → A) (hf : ∀ s a, qJ P r γ J s a ≤ qJ P r γ J s (f s)) (s : S) :
    ApproxOptRL.Shared.value P r γ (SampleComplexityRL.ApproxDP.detPolicy f) s ≥
      ApproxOptRL.Shared.value P r γ πstar s - 2 * bellmanError P r γ J / (1 - γ) := by sorry

end SampleComplexityRL.Mismeasure
