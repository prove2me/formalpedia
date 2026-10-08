-- Prove2me | Theorems.Thm_SampleComplexityRL_Mismeasure_napi_q_eq_and_advantage_le
-- name    : SampleComplexityRL.Mismeasure.napi_q_eq_and_advantage_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:53.664013+00:00
-- url     : https://prove2.me/theorems/364f26aa-98d5-41a8-80fd-3619680c60c6
-- title:
--   Lemma 5.3.1 — NAPI's output policy has Q_{π̃,t} = Q_{π,t} and A_{π̃,t}(s,a) ≤ ε_t(s)
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set, $P$ a transition kernel, $r:S\times A\to[0,1]$ a reward function and $T\ge1$. Run $T$-step non-stationary approximate policy iteration (NAPI, Algorithm 6) from an arbitrary deterministic policy, with an arbitrary PolicyChooser returning the deterministic decision rules $h_{T-1},\dots,h_0$ at the updates $t=T-1,\dots,0$. Let $\tilde\pi=(h_0,\dots,h_{T-1})$ be the output policy, and for an update $t\in\{0,\dots,T-1\}$ let $\pi$ be the input policy to the PolicyChooser at that update. Then for all states $s$ and actions $a$,
--   $$Q_{\tilde\pi,t}(s,a)=Q_{\pi,t}(s,a),$$
--   and, with the per state error $\varepsilon_t(s)=\max_{a'}Q_{\pi,t}(s,a')-Q_{\pi,t}(s,h_t(s))$,
--   $$A_{\tilde\pi,t}(s,a)\le\varepsilon_t(s).$$
--
--   The errors of the PolicyChooser, measured against its input policies, therefore bound the advantages of the output policy directly; this is what lets NAPI avoid max-norm error bounds.
--
--   **Formalization Note** The run is the explicit recursion `napiPolicy` (input policy at update $t$: `napiPolicy T init h (t+1)`; output: `napiPolicy T init h 0`), with the loop over $t=T-1,\dots,0$ (the printed range $T-1,\dots,1$ is corrected). Deterministic policies enter through their indicator policies.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 63, Lemma 5.3.1 (Algorithm 6 on p. 62)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_SampleComplexityRL_Mismeasure_TEpoch
import Definitions.Def_SampleComplexityRL_Mismeasure_NAPI
open FoundationsML.ReinforcementLearning

namespace SampleComplexityRL.Mismeasure

/-- **Lemma 5.3.1** (Kakade 2003, p. 63). Run `T`-step NAPI (Algorithm 6, updates
`t = T-1, …, 0`) from a deterministic policy `init` with an arbitrary PolicyChooser returning the
decision rules `h t`. Let `π̃ = napiPolicy T init h 0` be the output policy and, for an update
`t < T`, let `π = napiPolicy T init h (t+1)` be the input policy to the PolicyChooser at that update.
Then for all `s`, `a`: `Q_{π̃,t}(s,a) = Q_{π,t}(s,a)` and `A_{π̃,t}(s,a) ≤ ε_t(s)`, where
`ε_t(s) = max_a Q_{π,t}(s,a) - Q_{π,t}(s,h_t(s))` is the per state error. -/
theorem napi_q_eq_and_advantage_le {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (T : ℕ) (hT : 0 < T)
    (init : ℕ → S → A) (h : ℕ → S → A) (t : ℕ) (ht : t < T) :
    (∀ s a, SampleComplexityRL.PolicyGrad.tQValue P r T (detNSPolicy (napiPolicy T init h 0)) t s a =
        SampleComplexityRL.PolicyGrad.tQValue P r T (detNSPolicy (napiPolicy T init h (t + 1))) t s a) ∧
    (∀ s a, SampleComplexityRL.PolicyGrad.tAdvantage P r T (detNSPolicy (napiPolicy T init h 0)) t s a ≤
        perStateError P r T (napiPolicy T init h (t + 1)) t (h t) s) := by sorry

end SampleComplexityRL.Mismeasure
