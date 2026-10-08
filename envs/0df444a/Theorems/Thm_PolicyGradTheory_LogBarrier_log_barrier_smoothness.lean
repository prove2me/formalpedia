-- Prove2me | Theorems.Thm_PolicyGradTheory_LogBarrier_log_barrier_smoothness
-- name    : PolicyGradTheory.LogBarrier.log_barrier_smoothness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:59.645986+00:00
-- url     : https://prove2.me/theorems/df6ec2a0-0bc2-46e2-9c6d-6ecca51bac2a
-- title:
--   Lemma D.4, p. 75 — L_λ is β_λ-smooth with β_λ = 8/(1−γ)³ + 2λ/|S|
-- statement:
--   Let $(P,r,\gamma)$ be a finite MDP, $\mu\in\Delta(\mathcal S)$ and $\lambda\ge0$, and let $L_\lambda$ be the log barrier regularized objective over softmax policies. For all parameters $\theta,\theta'$,
--   $$
--   \|\nabla_\theta L_\lambda(\theta)-\nabla_\theta L_\lambda(\theta')\|_2\le\beta_\lambda\,\|\theta-\theta'\|_2,\qquad\beta_\lambda=\frac{8}{(1-\gamma)^3}+\frac{2\lambda}{|\mathcal S|}.
--   $$
--
--   Smoothness fixes the step size $\eta=1/\beta_\lambda$ of gradient ascent in Corollary 5.1 and enters its iteration count.
--
--   **Formalization Note.** The page's $L_\lambda$ in Lemma D.4 omits the additive constant $\lambda\log|\mathcal A|$ of (12); a constant does not change the gradient, so the same objective is used. $\lambda\ge0$ is the page's regularization parameter; the action set is nonempty.
-- source:
--   arXiv:1908.00261v5, Lemma D.4, p. 75

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_LogBarrier_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.LogBarrier

/-- Lemma D.4 (smoothness for log barrier regularized softmax), arXiv:1908.00261v5, p. 75:
`‖∇_θ L_λ(θ) − ∇_θ L_λ(θ')‖₂ ≤ β_λ ‖θ − θ'‖₂` with `β_λ = 8/(1−γ)³ + 2λ/|S|`. The constant
`λ log |A|` of (12), absent from the page's `L_λ` in D.4, does not change the gradient. -/
theorem log_barrier_smoothness {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ) (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (lam : ℝ) (hlam : 0 ≤ lam)
    (θ θ' : EuclideanSpace ℝ (S × A)) :
    ‖gradient (logBarrierObj P r γ μ lam) θ - gradient (logBarrierObj P r γ μ lam) θ'‖ ≤
      betaLam S γ lam * ‖θ - θ'‖ := by sorry

end PolicyGradTheory.LogBarrier
