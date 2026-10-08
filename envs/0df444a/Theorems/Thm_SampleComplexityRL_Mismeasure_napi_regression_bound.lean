-- Prove2me | Theorems.Thm_SampleComplexityRL_Mismeasure_napi_regression_bound
-- name    : SampleComplexityRL.Mismeasure.napi_regression_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:45.708731+00:00
-- url     : https://prove2.me/theorems/05185744-75f5-4806-aded-ad995985c5f3
-- title:
--   Theorem 5.3.2 — NAPI with RegressionPolicyChooser: V_π(s₀) ≥ V_{π′}(s₀) − 2T·E_{(s,t)∼d_{π′,s₀}}[ε̃_t(s)]
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set, $P(s'\mid s,a)$ a transition kernel, $r:S\times A\to[0,1]$ a reward function and $T\ge1$ a horizon, with normalized values $V_\pi=\frac1T\mathbb E[\sum_{t=0}^{T-1}r(s_t,a_t)]$.
--
--   Run $T$-step non-stationary approximate policy iteration (NAPI, Algorithm 6) with RegressionPolicyChooser (Algorithm 7): start from an arbitrary deterministic policy; at the updates $t=T-1,\dots,0$, with $\pi^{(t+1)}$ the current (input) policy, a regressor returns an arbitrary approximation $\tilde Q_t$ of $Q_{\pi^{(t+1)},t}$, the decision rule $h_t$ is greedy with respect to $\tilde Q_t$, and the decision rule at time $t$ is set to $h_t$. Let $\pi=(h_0,\dots,h_{T-1})$ be the returned policy and
--   $$\tilde\varepsilon_t(s)=\max_{a\in A}\big|Q_{\pi^{(t+1)},t}(s,a)-\tilde Q_t(s,a)\big|$$
--   the per state regression error at update $t$. Then for every policy $\pi'$ (possibly stochastic and non-stationary) and every state $s_0$,
--   $$V_\pi(s_0)\;\ge\;V_{\pi'}(s_0)-2T\,\mathbb E_{(s,t)\sim d_{\pi',s_0}}\big[\tilde\varepsilon_t(s)\big]=V_{\pi'}(s_0)-2T\sum_{t=0}^{T-1}\sum_{s\in S}d_{\pi',s_0}(s,t)\,\tilde\varepsilon_t(s),$$
--   where $d_{\pi',s_0}(s,t)=\frac1T\Pr(s_t=s\mid\pi',s_0)$ is the future state-time distribution of $\pi'$.
--
--   Taking $\pi'$ optimal, the loss of NAPI is controlled by the regression error averaged under the state-time distribution of an optimal policy, an average error rather than a max-norm error, and with a single factor of $T$.
--
--   **Formalization Note** The run is explicit: `napiPolicy T init h t` is the policy after the updates $T-1,\dots,t$, the regression error of update $t$ is measured against the input policy `napiPolicy T init h (t+1)`, and the returned policy is `napiPolicy T init h 0`. The thesis prints the loop as "For $t=T-1,\dots,1$"; the decision rule at time $0$ would then stay random and the theorem would fail, so the loop runs to $t=0$ as in the proof and in Algorithms 8–9. The regressor outputs $\tilde Q_t$ are arbitrary functions. Epochs are 0-based.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 64, Theorem 5.3.2 (Algorithm 6 p. 62, Algorithm 7 p. 64)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_SampleComplexityRL_Mismeasure_TEpoch
import Definitions.Def_SampleComplexityRL_Mismeasure_NAPI
open FoundationsML.ReinforcementLearning

namespace SampleComplexityRL.Mismeasure

/-- **Theorem 5.3.2** (Kakade 2003, p. 64). Run `T`-step NAPI (Algorithm 6, updates
`t = T-1, …, 0`; the printed loop "`T-1, … 1`" omits `t = 0` and is corrected) from a
deterministic policy `init`, with RegressionPolicyChooser (Algorithm 7): at update `t` the input
policy is `napiPolicy T init h (t+1)`, the regressor returns an arbitrary `Qtil t` approximating its
`Q_{·,t}`, and the returned decision rule `h t` is greedy for `Qtil t`. Let
`π = napiPolicy T init h 0` be the returned policy and `ε̃_t(s)` the per state regression error
measured against the input policy of update `t`. Then for every policy `π'` and every state `s₀`,
`V_π(s₀) ≥ V_{π'}(s₀) - 2T E_{(s,t) ∼ d_{π',s₀}}[ε̃_t(s)]`. -/
theorem napi_regression_bound {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (T : ℕ) (hT : 0 < T)
    (init : ℕ → S → A) (Qtil : ℕ → S → A → ℝ) (h : ℕ → S → A)
    (hgreedy : ∀ t, t < T → ∀ s a, Qtil t s a ≤ Qtil t s (h t s))
    (π' : SampleComplexityRL.PolicyGrad.NSPolicy S A) (hπ' : SampleComplexityRL.PolicyGrad.IsNSPolicy T π') (s₀ : S) :
    SampleComplexityRL.PolicyGrad.value P r T (detNSPolicy (napiPolicy T init h 0)) s₀ ≥
      SampleComplexityRL.PolicyGrad.value P r T π' s₀ - 2 * (T : ℝ) * ∑ t ∈ Finset.range T, ∑ s,
        stateTimeDist P π' s₀ T s t *
          regressionError P r T (napiPolicy T init h (t + 1)) t (Qtil t) s := by sorry

end SampleComplexityRL.Mismeasure
