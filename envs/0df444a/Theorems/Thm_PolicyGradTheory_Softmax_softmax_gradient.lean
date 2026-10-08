-- Prove2me | Theorems.Thm_PolicyGradTheory_Softmax_softmax_gradient
-- name    : PolicyGradTheory.Softmax.softmax_gradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:35:26.906237+00:00
-- url     : https://prove2.me/theorems/b46363d2-64ce-42b1-bf6a-0bdb1ab44bd4
-- title:
--   Lemma C.1, p. 59 — softmax policy gradient ∂V^{π_θ}(µ)/∂θ_{s,a} = (1/(1−γ)) d^{π_θ}_µ(s) π_θ(a|s) A^{π_θ}(s,a)
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite MDP with rewards in $[0,1]$ and $\gamma\in[0,1)$, let $\mu$ be a weighting of the states, and let $\pi_\theta$ be the softmax policy with parameters $\theta\in\mathbb R^{|\mathcal S||\mathcal A|}$. Write $d^{\pi_\theta}_\mu$ for the discounted state visitation distribution started from $\mu$ and $A^{\pi_\theta}$ for the advantage function. Then for every parameter $\theta$, state $s$ and action $a$,
--   $$
--   \frac{\partial V^{\pi_\theta}(\mu)}{\partial\theta_{s,a}}=\frac{1}{1-\gamma}\,d^{\pi_\theta}_\mu(s)\,\pi_\theta(a\mid s)\,A^{\pi_\theta}(s,a).
--   $$
--
--   This closed form (also displayed as (10) in §5) drives the whole analysis of softmax policy gradient: the update of $\theta_{s,a}$ has the sign of the advantage and is damped by $\pi_\theta(a\mid s)$ and by the visitation weight of $s$.
--
--   **Formalization Note** The left side is the $(s,a)$ coordinate of Mathlib's `gradient` on the Euclidean space $\mathbb R^{\mathcal S\times\mathcal A}$. Both sides are linear in $\mu$, so the identity is stated for every real weighting $\mu$; the paper's $\mu\in\Delta(\mathcal S)$ is a special case.
-- source:
--   arXiv:1908.00261v5, Lemma C.1, p. 59 (also (10), p. 18)

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
open FoundationsML.ReinforcementLearning Filter Topology

namespace PolicyGradTheory.Softmax

/-- Lemma C.1 (arXiv:1908.00261v5, p. 59), also (10) (p. 18): for the softmax policy class,
`∂V^{π_θ}(µ)/∂θ_{s,a} = (1/(1−γ)) d^{π_θ}_µ(s) π_θ(a|s) A^{π_θ}(s,a)`. -/
theorem softmax_gradient {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    gradient (softmaxValue P r γ μ) θ (s, a) =
      1 / (1 - γ) * PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ) P γ μ s * softmaxPolicy θ s a *
        PolicyGradTheory.ProjGA.advantage (softmaxPolicy θ) P r γ s a := by sorry

end PolicyGradTheory.Softmax
