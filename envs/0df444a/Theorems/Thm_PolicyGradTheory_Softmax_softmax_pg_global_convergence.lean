-- Prove2me | Theorems.Thm_PolicyGradTheory_Softmax_softmax_pg_global_convergence
-- name    : PolicyGradTheory.Softmax.softmax_pg_global_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:51:43.578347+00:00
-- url     : https://prove2.me/theorems/c51129d7-3b2a-4ea7-8c45-31df76db995a
-- title:
--   Theorem 5.1, p. 18 — softmax policy gradient with µ > 0 and η ≤ (1−γ)³/8 has V^{(t)}(s) → V⋆(s) for every state s
-- statement:
--   **Global convergence of softmax policy gradient.** Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite MDP with finite nonempty action set, rewards $r(s,a)\in[0,1]$ and discount factor $\gamma\in[0,1)$, and let $\mu$ be a distribution on $\mathcal S$ that is strictly positive, $\mu(s)>0$ for every state $s$. For $\theta\in\mathbb R^{|\mathcal S||\mathcal A|}$ let $\pi_\theta(a\mid s)=\exp(\theta_{s,a})/\sum_{a'}\exp(\theta_{s,a'})$ be the softmax policy, and let $(\theta^{(t)})_{t\ge0}$ follow gradient ascent on $V^{\pi_\theta}(\mu)$,
--   $$
--   \theta^{(t+1)}=\theta^{(t)}+\eta\,\nabla_\theta V^{(t)}(\mu),
--   $$
--   from an arbitrary $\theta^{(0)}$, with step size $0<\eta\le(1-\gamma)^3/8$. Let $V^\star$ be the optimal value function. Then for every state $s$,
--   $$
--   V^{(t)}(s)\to V^\star(s)\qquad(t\to\infty),
--   $$
--   where $V^{(t)}=V^{\pi_{\theta^{(t)}}}$.
--
--   The softmax parameterization never reaches a deterministic policy, and its gradient vanishes near every nearly deterministic policy, so convergence to the optimum is not a consequence of first-order stationarity; the theorem shows that plain gradient ascent nonetheless reaches the optimal values in the limit, without any regularization.
--
--   **Formalization Note** $V^\star(s)$ is written as $V^{\pi^\star}(s)$ for a policy $\pi^\star$ that is optimal at every state simultaneously (it exists for finite MDPs, and $V^\star=V^{\pi^\star}$ is the paper's notation). The step size is required to be positive, which "gradient ascent" presupposes; the paper writes only $\eta\le(1-\gamma)^3/8$.
-- source:
--   arXiv:1908.00261v5, Theorem 5.1, p. 18 (update (11), p. 18; proof App. C.1, pp. 60–68)

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
open FoundationsML.ReinforcementLearning Filter Topology

namespace PolicyGradTheory.Softmax

/-- Theorem 5.1 (arXiv:1908.00261v5, p. 18): softmax policy gradient ascent (11) with a strictly
positive start distribution `µ` and step size `η ≤ (1−γ)³/8`, from any initial `θ^{(0)}`, has
`V^{(t)}(s) → V^⋆(s)` for every state `s`. -/
theorem softmax_pg_global_convergence {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsSoftmaxPGRun P r γ μ η θ)
    (hμpos : ∀ s, 0 < μ s) (hηle : η ≤ (1 - γ) ^ 3 / 8)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (hopt : IsOptimalPolicy πstar P r γ) :
    ∀ s, Tendsto (fun t => PolicyValue (softmaxPolicy (θ t)) P r γ s) atTop
      (𝓝 (PolicyValue πstar P r γ s)) := by sorry

end PolicyGradTheory.Softmax
