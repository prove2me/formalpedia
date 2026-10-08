-- Prove2me | Theorems.Thm_SampleComplexityRL_MuPolicySearch_mu_optimality
-- name    : SampleComplexityRL.MuPolicySearch.mu_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:46.851277+00:00
-- url     : https://prove2.me/theorems/ee0970a3-1a4b-4a35-bebb-a6807098f470
-- title:
--   Theorem 6.3.1 (μ-Optimality) — if A_{π,t}(μ,h) ≤ ε/T on Π₁ then V_π(s₀) ≥ V_{π′}(s₀) − ε − T‖d_{π′,s₀} − μ‖₁ on Π₁^T
-- statement:
--   Let $M$ be a T-epoch MDP with finite state set $S$, finite nonempty action set $A$, transition kernel $P$, rewards $r(s,a)\in[0,1]$, horizon $T\ge1$ and the normalized values of Definition 2.2.1. Let $\Pi_1$ be a set of deterministic decision rules $h:S\to A$, let $\Pi=\Pi_1^T$ be the deterministic non-stationary policies that use a rule of $\Pi_1$ at every epoch, and let $\mu$ be a μ-reset state-time distribution (conditionals $\mu(\cdot\mid t)$, joint law $\mu(s,t)=\mu(s\mid t)/T$). Let $\varepsilon\in\mathbb R$. Assume that a T-epoch policy $\pi$ satisfies, for all $h\in\Pi_1$ and $t<T$,
--   $$A_{\pi,t}(\mu,h)\le\frac{\varepsilon}{T}.$$
--   Then for all policies $\pi'\in\Pi$ and all start states $s_0$,
--   $$V_\pi(s_0)\ge V_{\pi'}(s_0)-\varepsilon-T\,\|d_{\pi',s_0}-\mu\|_1,$$
--   where $d_{\pi',s_0}$ is the future state-time distribution of $\pi'$ and $\|d_{\pi',s_0}-\mu\|_1=\sum_s\sum_{t<T}|d_{\pi',s_0}(s,t)-\mu(s,t)|$.
--
--   The theorem turns small advantages on average under a chosen reset distribution $\mu$ into a guarantee against every policy of the class, at every start state, with a penalty measured by how far that policy's future state-time distribution is from $\mu$.
--
--   **Formalization Note** The policy $\pi$ may be stochastic; the competitors $\pi'$ are deterministic and enter as indicator policies, as the chapter deals with deterministic classes only. $\varepsilon$ is unconstrained in sign, as in the source. If $\Pi_1$ is empty, $\Pi$ is empty and the conclusion holds vacuously, as it does in the source.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 75, Theorem 6.3.1

import Mathlib
import Definitions.Def_SampleComplexityRL_MuPolicySearch_MuReset

namespace SampleComplexityRL.MuPolicySearch

open FoundationsML.ReinforcementLearning

/-- Theorem 6.3.1 (μ-Optimality; Kakade 2003, p. 75). Let `Pi1` be a set of deterministic
decision rules and `μ` a μ-reset state-time distribution. If a T-epoch policy `π` satisfies
`A_{π,t}(μ,h) ≤ ε/T` for all `h ∈ Pi1` and `t < T`, then for every deterministic policy
`π' ∈ Π = Pi1^T` and every start state `s₀`,
`V_π(s₀) ≥ V_{π'}(s₀) − ε − T ‖d_{π',s₀} − μ‖₁`. -/
theorem mu_optimality {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (hT : 0 < T)
    (μ : ℕ → S → ℝ) (hμ : IsResetDist T μ) (Pi1 : Set (S → A)) (ε : ℝ)
    (π : SampleComplexityRL.PolicyGrad.NSPolicy S A) (hπ : SampleComplexityRL.PolicyGrad.IsNSPolicy T π)
    (hadv : ∀ h ∈ Pi1, ∀ t < T, muAdvantage P r T π μ t h ≤ ε / T) :
    ∀ π' : ℕ → S → A, InPolicyClass Pi1 T π' → ∀ s₀ : S,
      SampleComplexityRL.PolicyGrad.value P r T (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀ - ε -
          (T : ℝ) * stateTimeL1 T (SampleComplexityRL.Mismeasure.stateTimeDist P (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀ T) (resetJoint T μ) ≤
        SampleComplexityRL.PolicyGrad.value P r T π s₀ := by sorry

end SampleComplexityRL.MuPolicySearch
