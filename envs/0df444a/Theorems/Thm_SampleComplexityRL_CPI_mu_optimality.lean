-- Prove2me | Theorems.Thm_SampleComplexityRL_CPI_mu_optimality
-- name    : SampleComplexityRL.CPI.mu_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:37.468351+00:00
-- url     : https://prove2.me/theorems/105a5d0a-8000-444f-aa74-e83ed9901e82
-- title:
--   Theorem 7.3.1 — advantages at most ε/H under ν give $V_\pi(s_0)\ge V_{\pi'}(s_0)-\varepsilon-H\|d_{\pi',s_0}-\nu\|_1$
-- statement:
--   Consider a finite MDP with nonempty state set $S$, nonempty action set $A$, transition kernel $P$, rewards $r(s,a)\in[0,1]$ and discount $0\le\gamma<1$, with normalized values $V_\pi$ and advantages $A_\pi$. Let $H=1/(1-\gamma)$ and let $\Pi$ be a class of stationary policies. For a state distribution $\nu$ and a policy $h$ write $A_\pi(\nu,h)=\mathbb E_{s\sim\nu}\mathbb E_{a\sim h(\cdot\mid s)}[A_\pi(s,a)]$, and let $d_{\pi',s_0}$ be the discounted future state distribution of $\pi'$ started at $s_0$.
--
--   Let $\pi$ be a stationary policy and $\nu$ a distribution such that
--   $$A_\pi(\nu,h)\le\frac{\varepsilon}{H}\qquad\text{for all }h\in\Pi.$$
--   Then for every policy $\pi'\in\Pi$ and every state $s_0$,
--   $$V_\pi(s_0)\ \ge\ V_{\pi'}(s_0)-\varepsilon-H\,\|d_{\pi',s_0}-\nu\|_1,\qquad \|p-q\|_1=\sum_s|p(s)-q(s)|.$$
--
--   A policy whose average advantages under $\nu$ are small competes with every policy of the class whose future state distribution is close to $\nu$. With $\nu=d_{\pi,\mu}$ this is the guarantee that motivates the output condition of conservative policy iteration.
--
--   **Formalization Note** The hypothesis is on the advantage $A_\pi(\nu,h)$ of Definition 7.1.1, weighted by $\nu$, and not on the future advantage. The policy $\pi$ need not belong to $\Pi$, and $\varepsilon$ is any real number.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 89, Theorem 7.3.1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_CPI_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_CPI_ExactCPI
open ApproxOptRL.Shared ApproxOptRL.CPI FoundationsML.ReinforcementLearning

namespace SampleComplexityRL.CPI

/-- **Theorem 7.3.1** (Kakade 2003, p. 89). Let `Pi` be a class of stationary policies. If `π`
is a policy such that, for the distribution `ν` and every `h ∈ Pi`, `A_π(ν, h) ≤ ε/H`, then for
every `π' ∈ Pi` and every start state `s₀`,
`V_π(s₀) ≥ V_{π'}(s₀) − ε − H ‖d_{π',s₀} − ν‖₁`.
Normalized discounted values; `H = 1/(1 − γ)`; `A_π(ν, h)` is the advantage of Definition 7.1.1
(state weights `ν`, not the future distribution). -/
theorem mu_optimality {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty S] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (Pi : Set (S → A → ℝ)) (hPi : ∀ h ∈ Pi, IsPolicy h)
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (ν : S → ℝ) (hν : IsStateDist ν) (ε : ℝ)
    (hadv : ∀ h ∈ Pi, distAdvantage P r γ π ν h ≤ ε / horizon γ) :
    ∀ π' ∈ Pi, ∀ s₀ : S,
      value P r γ π' s₀ - ε - horizon γ * l1Dist (futureStateDist P γ π' (pointMass s₀)) ν ≤
        value P r γ π s₀ := by sorry

end SampleComplexityRL.CPI
