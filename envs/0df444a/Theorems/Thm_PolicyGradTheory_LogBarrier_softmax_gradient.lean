-- Prove2me | Theorems.Thm_PolicyGradTheory_LogBarrier_softmax_gradient
-- name    : PolicyGradTheory.LogBarrier.softmax_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:22.76768+00:00
-- url     : https://prove2.me/theorems/3e42df11-e073-4c91-a1b4-82f21cfa4a1b
-- title:
--   Lemma C.1, p. 59 — softmax policy gradient: ∂V^{π_θ}(µ)/∂θ_{s,a} = (1/(1−γ)) d^{π_θ}_µ(s) π_θ(a|s) A^{π_θ}(s,a)
-- statement:
--   Let $(P,r,\gamma)$ be a finite MDP, $\mu$ a weighting of the states and $\pi_\theta$ the softmax policy (3) with parameter $\theta\in\mathbb R^{|\mathcal S||\mathcal A|}$. For every state $s$ and action $a$,
--   $$
--   \frac{\partial V^{\pi_\theta}(\mu)}{\partial\theta_{s,a}}=\frac{1}{1-\gamma}\,d^{\pi_\theta}_\mu(s)\,\pi_\theta(a\mid s)\,A^{\pi_\theta}(s,a).
--   $$
--
--   This closed form of the softmax policy gradient is the basis of every softmax result of §5; adding the derivative of the log barrier gives (14).
--
--   **Formalization Note.** The partial derivative is the $(s,a)$ coordinate of Mathlib's `gradient` on `EuclideanSpace ℝ (S × A)`. The action set is assumed nonempty so that $\pi_\theta$ is a policy. The identity is linear in $\mu$, so it is stated for every $\mu:\mathcal S\to\mathbb R$; the page's $\mu\in\Delta(\mathcal S)$ is a special case.
-- source:
--   arXiv:1908.00261v5, Lemma C.1, p. 59 (also (10), p. 18)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_LogBarrier_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.LogBarrier

/-- Lemma C.1, arXiv:1908.00261v5, p. 59 (= (10), p. 18): for the softmax policy class,
`∂V^{π_θ}(µ)/∂θ_{s,a} = (1/(1−γ)) d^{π_θ}_µ(s) π_θ(a|s) A^{π_θ}(s,a)`. -/
theorem softmax_gradient {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    gradient (PolicyGradTheory.Softmax.softmaxValue P r γ μ) θ (s, a) =
      1 / (1 - γ) * PolicyGradTheory.ProjGA.visitation (PolicyGradTheory.Softmax.softmaxPolicy θ) P γ μ s * PolicyGradTheory.Softmax.softmaxPolicy θ s a *
        PolicyGradTheory.ProjGA.advantage (PolicyGradTheory.Softmax.softmaxPolicy θ) P r γ s a := by sorry

end PolicyGradTheory.LogBarrier
