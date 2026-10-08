-- Prove2me | Theorems.Thm_PolicyGradTheory_LogBarrier_log_barrier_gradient
-- name    : PolicyGradTheory.LogBarrier.log_barrier_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:37.428067+00:00
-- url     : https://prove2.me/theorems/254def51-6227-4009-9d01-f7acec8ea362
-- title:
--   (14), p. 20 — ∂L_λ(θ)/∂θ_{s,a} = (1/(1−γ)) d^{π_θ}_µ(s) π_θ(a|s) A^{π_θ}(s,a) + (λ/|S|)(1/|A| − π_θ(a|s))
-- statement:
--   Let $(P,r,\gamma)$ be a finite MDP, $\mu$ a weighting of the states, $\lambda$ a real number and $L_\lambda$ the log barrier regularized objective (12) over softmax policies. For every $\theta$, state $s$ and action $a$,
--   $$
--   \frac{\partial L_\lambda(\theta)}{\partial\theta_{s,a}}=\frac{1}{1-\gamma}\,d^{\pi_\theta}_\mu(s)\,\pi_\theta(a\mid s)\,A^{\pi_\theta}(s,a)+\frac{\lambda}{|\mathcal S|}\Big(\frac{1}{|\mathcal A|}-\pi_\theta(a\mid s)\Big).
--   $$
--
--   The second term pushes every action probability towards $1/|\mathcal A|$; the proof of Theorem 5.2 reads off from this display that actions with positive advantage keep probability at least $1/(2|\mathcal A|)$ at approximately stationary points.
--
--   **Formalization Note.** Partial derivatives are coordinates of Mathlib's `gradient` on `EuclideanSpace ℝ (S × A)`; the action set is nonempty. The identity is stated for every real $\lambda$ and every $\mu$, of which the page's setting is a special case.
-- source:
--   arXiv:1908.00261v5, §5.2, proof of Theorem 5.2, display (14), p. 20

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_LogBarrier_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.LogBarrier

/-- Display (14), proof of Theorem 5.2, arXiv:1908.00261v5, p. 20: the partial derivatives of
the log barrier regularized objective (12),
`∂L_λ(θ)/∂θ_{s,a} = (1/(1−γ)) d^{π_θ}_µ(s) π_θ(a|s) A^{π_θ}(s,a) + (λ/|S|)(1/|A| − π_θ(a|s))`. -/
theorem log_barrier_gradient {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ) (μ : S → ℝ) (lam : ℝ) (θ : EuclideanSpace ℝ (S × A)) (s : S)
    (a : A) :
    gradient (logBarrierObj P r γ μ lam) θ (s, a) =
      1 / (1 - γ) * PolicyGradTheory.ProjGA.visitation (PolicyGradTheory.Softmax.softmaxPolicy θ) P γ μ s * PolicyGradTheory.Softmax.softmaxPolicy θ s a *
          PolicyGradTheory.ProjGA.advantage (PolicyGradTheory.Softmax.softmaxPolicy θ) P r γ s a
        + lam / (Fintype.card S : ℝ) * (1 / (Fintype.card A : ℝ) - PolicyGradTheory.Softmax.softmaxPolicy θ s a) := by sorry

end PolicyGradTheory.LogBarrier
