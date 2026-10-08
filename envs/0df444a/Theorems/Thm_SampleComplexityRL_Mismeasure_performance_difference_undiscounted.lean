-- Prove2me | Theorems.Thm_SampleComplexityRL_Mismeasure_performance_difference_undiscounted
-- name    : SampleComplexityRL.Mismeasure.performance_difference_undiscounted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:59.531001+00:00
-- url     : https://prove2.me/theorems/effc9903-a843-4296-8346-87593cfe593e
-- title:
--   Lemma 5.2.1 (undiscounted) — performance difference: V_{π′}(s₀) − V_π(s₀) = T·E_{(s,t)∼d_{π′,s₀}}E_{a∼π′}[A_{π,t}(s,a)]
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set, $P(s'\mid s,a)$ a transition kernel, $r:S\times A\to[0,1]$ a reward function and $T\ge1$ a horizon. Let $V_\pi$, $A_{\pi,t}$ and $d_{\pi,s_0}$ be the normalized value, the $t$-step undiscounted advantage and the future state-time distribution $d_{\pi,s_0}(s,t)=\frac1T\Pr(s_t=s\mid\pi,s_0)$.
--
--   For all (possibly stochastic, non-stationary) policies $\pi$ and $\pi'$ and every start state $s_0$,
--   $$V_{\pi'}(s_0)-V_\pi(s_0)=T\,\mathbb E_{(s,t)\sim d_{\pi',s_0}}\,\mathbb E_{a\sim\pi'(\cdot\mid s,t)}\big[A_{\pi,t}(s,a)\big]=T\sum_{t=0}^{T-1}\sum_{s\in S}d_{\pi',s_0}(s,t)\sum_{a\in A}\pi'(a\mid s,t)\,A_{\pi,t}(s,a).$$
--
--   The difference of two policies' values is thus expressed through the advantages of one policy averaged under the state-time distribution of the other, not through a max norm. This identity drives the analysis of non-stationary approximate policy iteration (Theorem 5.3.2) and of μ-policy search in the next chapter.
--
--   **Formalization Note** This item is the undiscounted half of Lemma 5.2.1; the discounted half is the published `ApproxOptRL.CPI.performance_difference` (with start distribution $\mu$ in place of $s_0$). Epochs are 0-based; the factor $1/T$ sits inside $d_{\pi',s_0}$ and the values.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 59, Lemma 5.2.1 (undiscounted case); proof p. 60

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_SampleComplexityRL_Mismeasure_TEpoch
open FoundationsML.ReinforcementLearning

namespace SampleComplexityRL.Mismeasure

/-- **Lemma 5.2.1, undiscounted half** (Kakade 2003, p. 59). In a `T`-epoch MDP (finite `S`, `A`,
transition kernel `P`, rewards in `[0,1]`, `T ≥ 1`), for all policies `π`, `π'` and all `s₀`,
`V_{π'}(s₀) - V_π(s₀) = T E_{(s,t) ∼ d_{π',s₀}} E_{a ∼ π'(·|s,t)}[A_{π,t}(s,a)]`.
The state-time distribution `d_{π',s₀}` (Definition 4.2.1) carries the factor `1/T`;
times are 0-based. -/
theorem performance_difference_undiscounted {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (T : ℕ) (hT : 0 < T)
    (π π' : SampleComplexityRL.PolicyGrad.NSPolicy S A) (hπ : SampleComplexityRL.PolicyGrad.IsNSPolicy T π) (hπ' : SampleComplexityRL.PolicyGrad.IsNSPolicy T π') (s₀ : S) :
    SampleComplexityRL.PolicyGrad.value P r T π' s₀ - SampleComplexityRL.PolicyGrad.value P r T π s₀ =
      (T : ℝ) * ∑ t ∈ Finset.range T, ∑ s, stateTimeDist P π' s₀ T s t *
        ∑ a, π' t s a * SampleComplexityRL.PolicyGrad.tAdvantage P r T π t s a := by sorry

end SampleComplexityRL.Mismeasure
