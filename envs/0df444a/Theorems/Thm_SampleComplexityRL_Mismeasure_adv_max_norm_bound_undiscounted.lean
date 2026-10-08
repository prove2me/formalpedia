-- Prove2me | Theorems.Thm_SampleComplexityRL_Mismeasure_adv_max_norm_bound_undiscounted
-- name    : SampleComplexityRL.Mismeasure.adv_max_norm_bound_undiscounted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:46.274455+00:00
-- url     : https://prove2.me/theorems/ff669cb4-0035-4600-a4ce-3787e02dd9f9
-- title:
--   Corollary 5.2.2 (undiscounted) — V_π(s₀) ≥ V*(s₀) − T‖A_{π,t}‖∞
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set, $P$ a transition kernel, $r:S\times A\to[0,1]$ a reward function and $T\ge1$. Let $V^*(s_0)=\sup_{\pi'}V_{\pi'}(s_0)$ be the optimal normalized value, the supremum over all policies of the $T$-epoch MDP. For every policy $\pi$ and every state $s_0$,
--   $$V_\pi(s_0)\;\ge\;V^*(s_0)-T\,\|A_{\pi,t}\|_\infty,\qquad \|A_{\pi,t}\|_\infty=\max_{0\le t\le T-1}\ \max_{s\in S,\,a\in A}\big|A_{\pi,t}(s,a)\big|.$$
--
--   This is the max-norm consequence of the performance difference lemma, analogous to the Williams–Baird bound; it hides the dependence on the state-time distribution of an optimal policy.
--
--   **Formalization Note** The printed $\|A_{\pi,t}\|_\infty$ leaves $t$ free; it is read as the maximum over all epochs $t<T$ and all state-action pairs, the reading the corollary needs. $V^*$ is the supremum over the subtype of valid policies.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 61, Corollary 5.2.2 (undiscounted case)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_SampleComplexityRL_Mismeasure_TEpoch
open FoundationsML.ReinforcementLearning

namespace SampleComplexityRL.Mismeasure

/-- **Corollary 5.2.2, undiscounted half** (Kakade 2003, p. 61). In a `T`-epoch MDP (finite `S`,
`A`, transition kernel `P`, rewards in `[0,1]`, `T ≥ 1`), for every policy `π` and every `s₀`,
`V_π(s₀) ≥ V*(s₀) - T ‖A_{π,t}‖_∞`, where `V* = optTValue … 0` is the supremum over all policies
(Definition 2.2.5) and `‖A_{π,t}‖_∞` is read as `max_{0 ≤ t < T} max_{s,a} |A_{π,t}(s,a)|`
(the printed statement leaves `t` free). -/
theorem adv_max_norm_bound_undiscounted {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (T : ℕ) (hT : 0 < T)
    (π : SampleComplexityRL.PolicyGrad.NSPolicy S A) (hπ : SampleComplexityRL.PolicyGrad.IsNSPolicy T π) (s₀ : S) :
    SampleComplexityRL.PolicyGrad.value P r T π s₀ ≥ optTValue P r T 0 s₀ -
      (T : ℝ) * (Finset.range T).sup' (Finset.nonempty_range_iff.mpr hT.ne')
        (fun t => ‖fun s a => SampleComplexityRL.PolicyGrad.tAdvantage P r T π t s a‖) := by sorry

end SampleComplexityRL.Mismeasure
