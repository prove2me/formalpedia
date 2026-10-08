-- Prove2me | Theorems.Thm_SampleComplexityRL_Mismeasure_adv_max_norm_bound_discounted
-- name    : SampleComplexityRL.Mismeasure.adv_max_norm_bound_discounted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:07.84118+00:00
-- url     : https://prove2.me/theorems/7938333a-f82f-4274-bc23-70a8fa7d3d7a
-- title:
--   Corollary 5.2.2 (discounted) — V_{π,γ}(s₀) ≥ V*_γ(s₀) − ‖A_{π,γ}‖∞/(1−γ)
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set, $P$ a transition kernel, $r:S\times A\to[0,1]$ a reward function and $0\le\gamma<1$. Let $V_{\pi,\gamma}=(1-\gamma)\mathbb E[\sum_t\gamma^tr(s_t,a_t)]$ be the normalized discounted value and $A_{\pi,\gamma}(s,a)=Q_{\pi,\gamma}(s,a)-V_{\pi,\gamma}(s)$ the advantage, and let $\pi^*$ be an optimal stationary policy, so that $V^*_\gamma=V_{\pi^*,\gamma}$. For every stationary policy $\pi$ and every state $s_0$,
--   $$V_{\pi,\gamma}(s_0)\;\ge\;V^*_\gamma(s_0)-\frac{1}{1-\gamma}\,\|A_{\pi,\gamma}\|_\infty,\qquad \|A_{\pi,\gamma}\|_\infty=\max_{s,a}|A_{\pi,\gamma}(s,a)|.$$
--
--   It is the discounted max-norm consequence of the performance difference lemma.
--
--   **Formalization Note** $V^*_\gamma$ is represented by the value of a stationary policy that is optimal among stationary stochastic policies at every state (`IsOptimalPolicy`); such policies exist in finite MDPs (thesis p. 26) and their value equals the thesis's supremum. The max norm is Mathlib's sup norm on `S → A → ℝ`.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 61, Corollary 5.2.2 (discounted case)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared ApproxOptRL.PolicyQuality

namespace SampleComplexityRL.Mismeasure

/-- **Corollary 5.2.2, discounted half** (Kakade 2003, p. 61). In the normalized discounted
model (finite `S`, `A`, transition kernel `P`, rewards in `[0,1]`, `0 ≤ γ < 1`), let `πstar` be an
optimal stationary policy, so that `V*_γ = V_{πstar,γ}`. For every stationary policy `π` and
every `s₀`, `V_{π,γ}(s₀) ≥ V*_γ(s₀) - (1/(1-γ)) ‖A_{π,γ}‖_∞`, with
`‖A_{π,γ}‖_∞ = max_{s,a} |A_{π,γ}(s,a)|`. -/
theorem adv_max_norm_bound_discounted {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (πstar : S → A → ℝ) (hstar : IsOptimalPolicy P r γ πstar)
    (π : S → A → ℝ) (hπ : IsPolicy π) (s₀ : S) :
    ApproxOptRL.Shared.value P r γ π s₀ ≥
      ApproxOptRL.Shared.value P r γ πstar s₀ -
        1 / (1 - γ) * ‖fun s a => ApproxOptRL.Shared.advantage P r γ π s a‖ := by sorry

end SampleComplexityRL.Mismeasure
