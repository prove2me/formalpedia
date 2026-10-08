-- Prove2me | Theorems.Thm_PolicyGradTheory_Softmax_softmax_pg_monotone
-- name    : PolicyGradTheory.Softmax.softmax_pg_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:50:11.09699+00:00
-- url     : https://prove2.me/theorems/a0ba0471-68dc-4aeb-8703-07e4a73985c0
-- title:
--   Lemma C.2, p. 60 — for η ≤ (1−γ)²/5, softmax policy gradient improves V^{(t)}(s) and Q^{(t)}(s,a) monotonically
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite MDP with rewards in $[0,1]$ and $\gamma\in[0,1)$, $\mathcal A$ nonempty, $\mu$ a probability distribution on $\mathcal S$, and let $(\theta^{(t)})_{t\ge0}$ be a run of softmax policy gradient ascent
--   $$
--   \theta^{(t+1)}=\theta^{(t)}+\eta\,\nabla_\theta V^{(t)}(\mu)
--   $$
--   from an arbitrary $\theta^{(0)}$, with step size $0<\eta\le(1-\gamma)^2/5$. Write $V^{(t)}$ and $Q^{(t)}$ for the value and state–action value functions of $\pi_{\theta^{(t)}}$. Then for every $t$, every state $s$ and every action $a$,
--   $$
--   V^{(t+1)}(s)\ge V^{(t)}(s),\qquad Q^{(t+1)}(s,a)\ge Q^{(t)}(s,a).
--   $$
--
--   The improvement is pointwise in the state, not only on average under $\mu$; this is what gives the limits $V^{(\infty)}$ and $Q^{(\infty)}$ of Lemma C.3.
--
--   **Formalization Note** $\mu$ need not be strictly positive here. The positivity $\eta>0$ is implicit in "gradient ascent" and is added explicitly.
-- source:
--   arXiv:1908.00261v5, Lemma C.2, p. 60 (updates (36), p. 60 = (11), p. 18)

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
open FoundationsML.ReinforcementLearning Filter Topology

namespace PolicyGradTheory.Softmax

/-- Lemma C.2 (arXiv:1908.00261v5, p. 60): for the softmax policy gradient updates (36) with
learning rate `η ≤ (1−γ)²/5`, `V^{(t+1)}(s) ≥ V^{(t)}(s)` and `Q^{(t+1)}(s,a) ≥ Q^{(t)}(s,a)` for
all states `s` and actions `a`. -/
theorem softmax_pg_monotone {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsSoftmaxPGRun P r γ μ η θ)
    (hηle : η ≤ (1 - γ) ^ 2 / 5) :
    ∀ t s a,
      PolicyValue (softmaxPolicy (θ t)) P r γ s ≤ PolicyValue (softmaxPolicy (θ (t + 1))) P r γ s ∧
      QFunction (softmaxPolicy (θ t)) P r γ s a ≤ QFunction (softmaxPolicy (θ (t + 1))) P r γ s a := by sorry

end PolicyGradTheory.Softmax
