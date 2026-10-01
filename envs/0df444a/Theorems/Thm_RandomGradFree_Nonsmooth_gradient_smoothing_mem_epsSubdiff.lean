-- Prove2me | Theorems.Thm_RandomGradFree_Nonsmooth_gradient_smoothing_mem_epsSubdiff
-- name    : RandomGradFree.Nonsmooth.gradient_smoothing_mem_epsSubdiff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T08:12:30.373679+00:00
-- url     : https://prove2.me/theorems/aed6b119-e1b9-4a2c-8005-daf0528bbce1
-- title:
--   Theorem 2 — $\nabla f_\mu(x) \in \partial_\epsilon f(x)$ with $\epsilon = \mu L_0(f) n^{1/2}$, $\mu \ge 0$
-- statement:
--   Let $E$ be a real inner product space of dimension $n$, let $f : E \to \mathbb R$ be convex and Lipschitz continuous with constant $L_0 \ge 0$, and let $\mu \ge 0$. Put $\epsilon = \mu L_0 n^{1/2}$. For $\mu > 0$ let $\nabla f_\mu(x)$ be the gradient of the Gaussian smoothing $f_\mu$; for $\mu = 0$ let $\nabla f_0(x) = \mathbb E_u[f'(x,u)\,u]$ be the limiting vector of Eq. (24), where $f'(x,u) = \lim_{\alpha \downarrow 0} (f(x+\alpha u) - f(x))/\alpha$ is the directional derivative. Then for every $x \in E$ the vector $\nabla f_\mu(x)$ is an $\epsilon$-subgradient of $f$ at $x$:
--
--   $$
--   f(y) \ge f(x) - \epsilon + \langle \nabla f_\mu(x), y - x\rangle \qquad \text{for all } y \in E .
--   $$
--
--   Thus the expected output of the random oracle is an approximate subgradient of the original nonsmooth function, with an error that vanishes linearly in $\mu$.
--
--   **Formalization Note** The $\epsilon$-subdifferential (p. 532) is written out as the inequality above. For $\mu > 0$ the vector is Mathlib's `gradient` of $f_\mu$ (which is differentiable, Eq. (21)); for $\mu = 0$ it is $\nabla f_0(x)$ of Eq. (24), written as the Gaussian expectation of the shared oracle at $\mu = 0$, $f'(x,u)\,u$ (Eq. (30), item 3). At $\mu = 0$ the statement is $\nabla f_0(x) \in \partial f(x)$, Eq. (31).
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 535, Theorem 2

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_RandomGradFree_Shared_oracle

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Nonsmooth

theorem gradient_smoothing_mem_epsSubdiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (L₀ : ℝ) (hL₀ : 0 ≤ L₀) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    ∀ y : E, f y ≥ f x - μ * L₀ * Real.sqrt (Module.finrank ℝ E)
      + inner ℝ (if μ = 0 then ∫ u, RandomGradFree.Shared.oracle f 0 x u ∂(stdGaussian E)
          else gradient (RandomGradFree.Shared.smoothing f μ) x) (y - x) := by sorry

end RandomGradFree.Nonsmooth
