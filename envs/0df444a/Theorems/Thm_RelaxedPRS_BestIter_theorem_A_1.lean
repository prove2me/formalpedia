-- Prove2me | Theorems.Thm_RelaxedPRS_BestIter_theorem_A_1
-- name    : RelaxedPRS.BestIter.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:32.672398+00:00
-- url     : https://prove2.me/theorems/73e2d024-3013-4b9a-ad7e-30ed6f1744ed
-- title:
--   Theorem A.1, p. 31 — descent lemma (A.1) and Baillon–Haddad cocoercivity (A.2)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\beta > 0$, and let $h : \mathcal H \to \mathbb R$ be convex and differentiable with a $(1/\beta)$-Lipschitz gradient. Then for all $x, y \in \mathcal H$ the upper bound
--   $$h(x) \le h(y) + \langle x - y, \nabla h(y)\rangle + \frac{1}{2\beta}\|x - y\|^2 \tag{A.1}$$
--   and the cocoercive inequality
--   $$\beta\|\nabla h(x) - \nabla h(y)\|^2 \le \langle x - y, \nabla h(x) - \nabla h(y)\rangle \tag{A.2}$$
--   hold.
--
--   These are the two facts about smooth convex functions the proof of Proposition 3.1 uses: (A.1) bounds the function value at $x_g$ by its value at $x_f$, and (A.2) gives the lower bound on $S_f$.
--
--   **Formalization Note** The paper states the result for a closed, proper, convex, differentiable $g : \mathcal H \to (-\infty, \infty]$; a function differentiable at every point is finite everywhere, so it is taken real-valued. "$\nabla h$ is $(1/\beta)$-Lipschitz" is the published `IsSmoothConvex β h`.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 31, Theorem A.1, (A.1)–(A.2)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_RelaxedPRS_BestIter_Setting
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization Filter

namespace RelaxedPRS.BestIter

theorem theorem_A_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (β : ℝ) (hβ : 0 < β) (hh : IsSmoothConvex β h) :
    (∀ x y : H, h x ≤ h y + inner ℝ (x - y) (gradient h y) + 1 / (2 * β) * ‖x - y‖ ^ 2) ∧
    (∀ x y : H, β * ‖gradient h x - gradient h y‖ ^ 2 ≤
      inner ℝ (x - y) (gradient h x - gradient h y)) := by sorry

end RelaxedPRS.BestIter
