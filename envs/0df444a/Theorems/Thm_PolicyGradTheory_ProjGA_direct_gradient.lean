-- Prove2me | Theorems.Thm_PolicyGradTheory_ProjGA_direct_gradient
-- name    : PolicyGradTheory.ProjGA.direct_gradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:44:48.647197+00:00
-- url     : https://prove2.me/theorems/4f4b3118-2ac0-406d-a1fb-b53c8e184e56
-- title:
--   (7), §4, p. 13 — gradient of the direct parameterization: ∂V^π(μ)/∂π(a|s) = (1/(1−γ)) d^π_μ(s) Q^π(s,a)
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite discounted MDP with rewards in $[0,1]$ and $\gamma\in[0,1)$, and let $\mu$ be a weighting of the start states. Under the direct parameterization $\pi(a\mid s)=\pi_{s,a}$, regard $V^\pi(\mu)$ as a function of the vector $\pi\in\mathbb R^{\mathcal S\times\mathcal A}$.
--
--   At every policy $\pi\in\Delta(\mathcal A)^{|\mathcal S|}$ and for all $s\in\mathcal S$, $a\in\mathcal A$,
--   $$
--   \frac{\partial V^\pi(\mu)}{\partial\pi(a\mid s)}=\frac1{1-\gamma}\,d^\pi_\mu(s)\,Q^\pi(s,a).
--   $$
--
--   This is the policy gradient for the direct parameterization. It is what the projected gradient ascent update (9) uses, and it is the link between the gradient and the advantage in the proof of the gradient domination lemma.
--
--   **Formalization Note** The claim is about the Euclidean gradient (Mathlib's `gradient`, which presupposes differentiability) of the map $\pi\mapsto V^\pi(\mu)$ on `EuclideanSpace ℝ (S × A)`, evaluated at a policy; its $(s,a)$ coordinate is the stated value. The value function is the series $\sum_t\gamma^t\cdots$, which converges on a neighbourhood of the simplex, so the gradient there is the genuine one. The page states (7) for a start distribution $\mu$; the identity is linear in $\mu$ and holds for every weighting, so no distribution hypothesis is assumed.
-- source:
--   arXiv:1908.00261v5, §4, (7), p. 13

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.ProjGA

/-- (7), §4, arXiv:1908.00261v5, p. 13: for the direct parameterization, at every policy `π`,
`∂V^π(μ)/∂π(a|s) = (1/(1−γ)) d^π_μ(s) Q^π(s,a)`; the Euclidean gradient of `π ↦ V^π(μ)` has
these coordinates. -/
theorem direct_gradient {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ) (μ : S → ℝ) :
    ∀ π ∈ simplexSet S A, ∀ (s : S) (a : A),
      gradient (directValue P r γ μ) π (s, a) =
        1 / (1 - γ) * visitation (asPolicy π) P γ μ s * QFunction (asPolicy π) P r γ s a := by sorry

end PolicyGradTheory.ProjGA
