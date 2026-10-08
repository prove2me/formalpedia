-- Prove2me | Theorems.Thm_SampleComplexityRL_MuPolicySearch_performance_difference
-- name    : SampleComplexityRL.MuPolicySearch.performance_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:46.68706+00:00
-- url     : https://prove2.me/theorems/3b66b7dc-7f4d-4694-b004-bb4c218f5ac5
-- title:
--   Lemma 5.2.1 (undiscounted) — performance difference V_{π′}(s₀) − V_π(s₀) = T E_{d_{π′,s₀}} E_{π′}[A_{π,t}]
-- statement:
--   Let $M$ be a T-epoch MDP with finite state set $S$, finite nonempty action set $A$, transition kernel $P$, rewards $r(s,a)\in[0,1]$ and horizon $T\ge1$, with the normalized values of Definition 2.2.1. For all valid T-epoch policies $\pi,\pi'$ and every start state $s_0$,
--   $$V_{\pi'}(s_0)-V_\pi(s_0)=T\,\mathbb E_{(s,t)\sim d_{\pi',s_0}}\,\mathbb E_{a\sim\pi'(\cdot\mid s,t)}\big[A_{\pi,t}(s,a)\big],$$
--   where $d_{\pi',s_0}$ is the future state-time distribution of $\pi'$ on $S\times\{0,\dots,T-1\}$ and $A_{\pi,t}$ the advantage of $\pi$ at epoch $t$.
--
--   The identity expresses the gap between two policies through the advantages of one of them, averaged over the states and times the other one visits. It is the starting point of the μ-optimality guarantee of Chapter 6.
--
--   **Formalization Note** The expectation over $d_{\pi',s_0}$ is the finite sum $\sum_{s}\sum_{t<T}d_{\pi',s_0}(s,t)\sum_a\pi'(a\mid s,t)A_{\pi,t}(s,a)$. This is the undiscounted half of the thesis's Lemma 5.2.1; the discounted half is a separate platform statement and is not restated here. The same undiscounted statement is drafted independently in the Chapter 5 mission of this series, over a copy of the same T-epoch definitions.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 59, Lemma 5.2.1 (Undiscounted)

import Mathlib
import Definitions.Def_SampleComplexityRL_Mismeasure_TEpoch
import Definitions.Def_SampleComplexityRL_PolicyGrad_TEpoch

namespace SampleComplexityRL.MuPolicySearch

open FoundationsML.ReinforcementLearning

/-- Lemma 5.2.1, undiscounted half (Kakade 2003, p. 59): for all T-epoch policies `π, π'` and
every start state `s₀`,
`V_{π'}(s₀) − V_π(s₀) = T · E_{(s,t) ∼ d_{π',s₀}} E_{a ∼ π'(·|s,t)}[A_{π,t}(s,a)]`.
The expectation over `d_{π',s₀}` is the finite sum over `S × {0, …, T-1}`. -/
theorem performance_difference {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (hT : 0 < T)
    (π π' : SampleComplexityRL.PolicyGrad.NSPolicy S A) (hπ : SampleComplexityRL.PolicyGrad.IsNSPolicy T π) (hπ' : SampleComplexityRL.PolicyGrad.IsNSPolicy T π') (s₀ : S) :
    SampleComplexityRL.PolicyGrad.value P r T π' s₀ - SampleComplexityRL.PolicyGrad.value P r T π s₀ =
      (T : ℝ) * ∑ s, ∑ t ∈ Finset.range T,
        SampleComplexityRL.Mismeasure.stateTimeDist P π' s₀ T s t * ∑ a, π' t s a * SampleComplexityRL.PolicyGrad.tAdvantage P r T π t s a := by sorry

end SampleComplexityRL.MuPolicySearch
