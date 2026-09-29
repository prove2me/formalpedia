-- Prove2me | Theorems.Thm_RandomGradFree_Nonsmooth_smoothing_convex
-- name    : RandomGradFree.Nonsmooth.smoothing_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T07:40:37.659985+00:00
-- url     : https://prove2.me/theorems/d0e6d666-9154-4f52-a7dd-d7191bc89ebe
-- title:
--   Section 2 — if $f$ is convex then $f_\mu$ is convex
-- statement:
--   Let $f : E \to \mathbb R$ be convex and let $\mu \ge 0$ be such that the Gaussian average $\mathbb E_u f(x+\mu u)$ exists (is finite) at every $x \in E$. Then the Gaussian smoothing
--
--   $$
--   f_\mu(x) = \mathbb E_u f(x+\mu u)
--   $$
--
--   is a convex function on $E$.
--
--   Convexity of $f_\mu$ is what lets the analysis of the random search method use the gradient inequality for $f_\mu$ along the iterates.
--
--   **Formalization Note** The paper states this for convex $f$, with $f_\mu$ implicitly finite. That implicit assumption is made explicit as integrability of $u \mapsto f(x+\mu u)$ against the standard Gaussian at every $x$ (without it the Bochner integral would be $0$ by convention). Lipschitz $f$, the setting of Theorem 6, satisfies it.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 533, Section 2, first bullet after Eq. (11)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Nonsmooth

theorem smoothing_convex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hint : ∀ x, Integrable (fun u => f (x + μ • u)) (stdGaussian E)) :
    ConvexOn ℝ Set.univ (RandomGradFree.Shared.smoothing f μ) := by sorry

end RandomGradFree.Nonsmooth
