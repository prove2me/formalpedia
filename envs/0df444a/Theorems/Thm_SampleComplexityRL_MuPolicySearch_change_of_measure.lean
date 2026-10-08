-- Prove2me | Theorems.Thm_SampleComplexityRL_MuPolicySearch_change_of_measure
-- name    : SampleComplexityRL.MuPolicySearch.change_of_measure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:52.028179+00:00
-- url     : https://prove2.me/theorems/cdc7fa5e-8102-4ddb-9444-03944eb09537
-- title:
--   p. 76, proof of Theorem 6.3.1 — change of measure from d_{π′,s₀} to μ at the cost T‖d_{π′,s₀} − μ‖₁
-- statement:
--   Let $M$ be a T-epoch MDP (finite $S$, finite nonempty $A$, kernel $P$, rewards in $[0,1]$, $T\ge1$) and let $\mu$ be a μ-reset state-time distribution, with conditionals $\mu(\cdot\mid t)$ and joint law $\mu(s,t)=\mu(s\mid t)/T$ on $S\times\{0,\dots,T-1\}$. For all valid T-epoch policies $\pi,\pi'$ and every start state $s_0$,
--   $$T\,\mathbb E_{(s,t)\sim d_{\pi',s_0}}\mathbb E_{a\sim\pi'(\cdot\mid s,t)}\big[A_{\pi,t}(s,a)\big]\le T\,\mathbb E_{(s,t)\sim\mu}\mathbb E_{a\sim\pi'(\cdot\mid s,t)}\big[A_{\pi,t}(s,a)\big]+T\,\|d_{\pi',s_0}-\mu\|_1,$$
--   where $\|d_{\pi',s_0}-\mu\|_1=\sum_s\sum_{t<T}|d_{\pi',s_0}(s,t)-\mu(s,t)|$.
--
--   This is the step of the proof of Theorem 6.3.1 that moves the average of the advantages from the "test" distribution $d_{\pi',s_0}$ to the "training" distribution $\mu$; it rests on the advantages of normalized values lying in $[-1,1]$.
--
--   **Formalization Note** Both expectations are finite sums over $S\times\{0,\dots,T-1\}$, against `stateTimeDist` and `resetJoint` respectively.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 76, display in the proof of Theorem 6.3.1 (second line)

import Mathlib
import Definitions.Def_SampleComplexityRL_MuPolicySearch_MuReset

namespace SampleComplexityRL.MuPolicySearch

open FoundationsML.ReinforcementLearning

/-- The change of measure in the proof of Theorem 6.3.1 (Kakade 2003, p. 76, second line of the
display): for T-epoch policies `π, π'`, a start state `s₀` and a μ-reset state-time distribution
`μ`,
`T E_{(s,t)∼d_{π',s₀}} E_{a∼π'(·|s,t)}[A_{π,t}(s,a)]
   ≤ T E_{(s,t)∼μ} E_{a∼π'(·|s,t)}[A_{π,t}(s,a)] + T ‖d_{π',s₀} − μ‖₁`,
where `μ(s,t) = μ(s|t)/T` is the joint distribution and `‖·‖₁` is the ℓ1 distance on
`S × {0, …, T-1}`. -/
theorem change_of_measure {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (hT : 0 < T)
    (μ : ℕ → S → ℝ) (hμ : IsResetDist T μ)
    (π π' : SampleComplexityRL.PolicyGrad.NSPolicy S A) (hπ : SampleComplexityRL.PolicyGrad.IsNSPolicy T π) (hπ' : SampleComplexityRL.PolicyGrad.IsNSPolicy T π') (s₀ : S) :
    (T : ℝ) * ∑ s, ∑ t ∈ Finset.range T,
        SampleComplexityRL.Mismeasure.stateTimeDist P π' s₀ T s t * ∑ a, π' t s a * SampleComplexityRL.PolicyGrad.tAdvantage P r T π t s a ≤
      (T : ℝ) * ∑ s, ∑ t ∈ Finset.range T,
          resetJoint T μ s t * ∑ a, π' t s a * SampleComplexityRL.PolicyGrad.tAdvantage P r T π t s a +
        (T : ℝ) * stateTimeL1 T (SampleComplexityRL.Mismeasure.stateTimeDist P π' s₀ T) (resetJoint T μ) := by sorry

end SampleComplexityRL.MuPolicySearch
