-- Prove2me | Theorems.Thm_SampleComplexityRL_MuPolicySearch_napi_output_values
-- name    : SampleComplexityRL.MuPolicySearch.napi_output_values
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:57.336985+00:00
-- url     : https://prove2.me/theorems/193fbaa7-fb6b-4068-9b1d-e62d567eb563
-- title:
--   Lemma 5.3.1 — NAPI's output policy has the input policy's Q_{π,t} and advantages at most ε_t(s)
-- statement:
--   Let $M$ be a T-epoch MDP (finite $S$, finite nonempty $A$, kernel $P$, rewards in $[0,1]$, $T\ge1$). Run T-step NAPI with deterministic policies: start from an arbitrary deterministic policy and, for $t=T-1,\dots,0$, set $\tilde\pi(\cdot,t)=h_t$, where $h_t$ is the decision rule returned by the PolicyChooser (arbitrary). Let $\tilde\pi=(h_0,\dots,h_{T-1})$ be the output policy and, for each $t<T$, let $\pi$ be the input policy to the PolicyChooser at update $t$. Then for all states $s$ and actions $a$:
--   1. $Q_{\tilde\pi,t}(s,a)=Q_{\pi,t}(s,a)$;
--   2. $A_{\tilde\pi,t}(s,a)\le\varepsilon_t(s)$, where $\varepsilon_t(s)=\max_{a'\in A}Q_{\pi,t}(s,a')-Q_{\pi,t}(s,h_t(s))$ is the per-state error at update $t$.
--
--   $$Q_{\tilde\pi,t}(s,a)=Q_{\pi,t}(s,a),\qquad A_{\tilde\pi,t}(s,a)\le\varepsilon_t(s).$$
--
--   The lemma converts the errors of the PolicyChooser, measured against its own input, into bounds on the advantages of the policy NAPI returns. It is the step that makes Exact μ-PolicySearch exact.
--
--   **Formalization Note** The input policy at update $t$ is `napiInput init h t` (decision rules $h_\tau$ at epochs $\tau>t$, the initial policy at $\tau\le t$) and the output is `napiOutput T init h`; deterministic policies enter as indicator policies. The same lemma is drafted in the Chapter 5 mission of this series.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 63, Lemma 5.3.1 (Algorithm 6, p. 62)

import Mathlib
import Definitions.Def_SampleComplexityRL_MuPolicySearch_MuReset

namespace SampleComplexityRL.MuPolicySearch

open FoundationsML.ReinforcementLearning

/-- Lemma 5.3.1 (Kakade 2003, p. 63), for a run of T-step NAPI with deterministic policies.
The run starts from an arbitrary deterministic policy `init`, and the update at time `t`
(backward, `t = T-1, …, 0`) sets `π̃(·,t) = h t`, where `h t` is whatever decision rule the
PolicyChooser returned. Let `π̃ = napiOutput T init h` be the output policy and
`napiInput init h t` the input policy to the PolicyChooser at update `t`. Then for every `t < T`
and all `s, a`:
1. `Q_{π̃,t}(s,a) = Q_{π,t}(s,a)`, `π` the input policy at update `t`;
2. `A_{π̃,t}(s,a) ≤ ε_t(s)`, where `ε_t(s) = max_a Q_{π,t}(s,a) − Q_{π,t}(s,h_t(s))`. -/
theorem napi_output_values {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (hT : 0 < T)
    (init h : ℕ → S → A) :
    ∀ t < T, ∀ (s : S) (a : A),
      SampleComplexityRL.PolicyGrad.tQValue P r T (SampleComplexityRL.Mismeasure.detNSPolicy (napiOutput T init h)) t s a =
          SampleComplexityRL.PolicyGrad.tQValue P r T (SampleComplexityRL.Mismeasure.detNSPolicy (napiInput init h t)) t s a ∧
        SampleComplexityRL.PolicyGrad.tAdvantage P r T (SampleComplexityRL.Mismeasure.detNSPolicy (napiOutput T init h)) t s a ≤
          perStateError P r T (SampleComplexityRL.Mismeasure.detNSPolicy (napiInput init h t)) t (h t) s := by sorry

end SampleComplexityRL.MuPolicySearch
