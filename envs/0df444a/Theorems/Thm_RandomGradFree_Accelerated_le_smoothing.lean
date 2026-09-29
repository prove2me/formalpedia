-- Prove2me | Theorems.Thm_RandomGradFree_Accelerated_le_smoothing
-- name    : RandomGradFree.Accelerated.le_smoothing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:09:41.020883+00:00
-- url     : https://prove2.me/theorems/2629c93f-166c-496e-b086-a9732c42b4ec
-- title:
--   Section 2, Eq. (11) — $f_\mu(x) \ge f(x)$ for convex $f$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, let $f : E \to \mathbb R$ be convex, let $\mu \ge 0$ and $x \in E$, and let $u$ be a standard Gaussian vector of $E$ such that $f(x + \mu u)$ is integrable. Then the Gaussian approximation $f_\mu(x) = \mathbb E_u f(x + \mu u)$ dominates $f$ at $x$:
--
--   $$
--   f_\mu(x) \ge f(x), \qquad x \in E.
--   $$
--
--   In the proof of Theorem 9 this turns the bound on $\mathbb E f_\mu(x_k)$ into a bound on $\mathbb E f(x_k)$.
--
--   **Formalization Note** The paper states (11) for any convex $f$ (a finite convex function on $E$ has a subgradient at every point) and takes the existence of the integral defining $f_\mu$ for granted. The Lean statement makes that integrability explicit as a hypothesis, since a Bochner integral of a non-integrable function is $0$.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 533, Section 2, Eq. (11)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem le_smoothing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E)
    (hint : Integrable (fun u => f (x + μ • u)) (stdGaussian E)) :
    f x ≤ RandomGradFree.Shared.smoothing f μ x := by sorry

end RandomGradFree.Accelerated
