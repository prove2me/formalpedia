-- Prove2me | Theorems.Thm_SampleComplexityRL_MuPolicySearch_exact_mu_policy_search
-- name    : SampleComplexityRL.MuPolicySearch.exact_mu_policy_search
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:33.968577+00:00
-- url     : https://prove2.me/theorems/6771608e-3f0f-4141-ad09-0bc4364c5d4a
-- title:
--   Theorem 6.3.2 — Exact μ-PolicySearch returns a policy with A_{π̃,t}(μ,h) ≤ 0 for all h ∈ Π₁, t < T
-- statement:
--   Let $M$ be a T-epoch MDP (finite $S$, finite nonempty $A$, kernel $P$, rewards in $[0,1]$, $T\ge1$), let $\Pi_1$ be a set of deterministic decision rules and let $\mu$ be a μ-reset state-time distribution. Run Exact μ-PolicySearch (Algorithm 8): starting from an arbitrary deterministic policy, for $t=T-1,\dots,0$ choose
--   $$h_t\in\arg\max_{h\in\Pi_1}Q_{\pi,t}(\mu,h),$$
--   where $\pi$ is the current policy at update $t$, and set $\tilde\pi(\cdot,t)=h_t$. Then the returned policy $\tilde\pi$ satisfies, for all $h\in\Pi_1$ and $t<T$,
--   $$A_{\tilde\pi,t}(\mu,h)\le0.$$
--
--   Combined with the μ-optimality theorem (Theorem 6.3.1) at $\varepsilon=0$, this says the exact algorithm returns a policy whose value at every start state $s_0$ is within $T\|d_{\pi',s_0}-\mu\|_1$ of every policy $\pi'\in\Pi_1^T$.
--
--   **Formalization Note** The argmax need not exist for an infinite class, so the run is described by hypotheses: at each update $t<T$, $h_t\in\Pi_1$ and $Q_{\pi,t}(\mu,h')\le Q_{\pi,t}(\mu,h_t)$ for every $h'\in\Pi_1$, with $\pi$ = `napiInput init h t`. The returned policy is `napiOutput T init h`.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 76, Theorem 6.3.2 (Algorithm 8, p. 76)

import Mathlib
import Definitions.Def_SampleComplexityRL_MuPolicySearch_MuReset

namespace SampleComplexityRL.MuPolicySearch

open FoundationsML.ReinforcementLearning

/-- Theorem 6.3.2 (Exact μ-PolicySearch; Kakade 2003, p. 76). A run of Algorithm 8 from an
arbitrary deterministic initial policy `init`: for `t = T-1, …, 0` the decision rule `h t` is an
exact maximizer over the class `Pi1` of `Q_{π,t}(μ, ·)`, where `π = napiInput init h t` is the
current policy at update `t`, and `π̃(·,t) = h t`. The returned policy
`π̃ = napiOutput T init h` satisfies `A_{π̃,t}(μ,h') ≤ 0` for all `h' ∈ Pi1` and `t < T`. -/
theorem exact_mu_policy_search {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (hT : 0 < T)
    (μ : ℕ → S → ℝ) (hμ : IsResetDist T μ) (Pi1 : Set (S → A))
    (init h : ℕ → S → A)
    (hrun : ∀ t < T, h t ∈ Pi1 ∧
      ∀ h' ∈ Pi1, muQValue P r T (SampleComplexityRL.Mismeasure.detNSPolicy (napiInput init h t)) μ t h' ≤
        muQValue P r T (SampleComplexityRL.Mismeasure.detNSPolicy (napiInput init h t)) μ t (h t)) :
    ∀ t < T, ∀ h' ∈ Pi1, muAdvantage P r T (SampleComplexityRL.Mismeasure.detNSPolicy (napiOutput T init h)) μ t h' ≤ 0 := by sorry

end SampleComplexityRL.MuPolicySearch
