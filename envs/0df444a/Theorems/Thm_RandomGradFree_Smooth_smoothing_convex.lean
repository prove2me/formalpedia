-- Prove2me | Theorems.Thm_RandomGradFree_Smooth_smoothing_convex
-- name    : RandomGradFree.Smooth.smoothing_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T09:41:36.20735+00:00
-- url     : https://prove2.me/theorems/57a9fd54-1f9f-40b2-a21c-d4419ca4eff4
-- title:
--   Section 2 — the Gaussian smoothing of a convex function is convex
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and let $f : E \to \mathbb R$ be convex, and let $\mu \ge 0$ be such that the Gaussian approximation $f_\mu(x) = \mathbb E_u f(x+\mu u)$ is finite at every $x \in E$ ($u$ a standard Gaussian vector). Then $f_\mu$ is convex on $E$.
--
--   Convexity of $f_\mu$ is what lets the analysis of the random gradient method use first-order convexity inequalities for $f_\mu$ along the iterates.
--
--   **Formalization Note** The paper states this for any convex $f$ and takes $f_\mu$ to be well defined. That implicit assumption is the hypothesis that $u \mapsto f(x+\mu u)$ is integrable against the standard Gaussian for every $x$, so $f_\mu$ is a genuine integral rather than the junk value $0$. It holds, for example, for every $f$ with a Lipschitz gradient.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 533, Section 2, first bullet ("If f is convex, then f_mu is also convex")

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

theorem smoothing_convex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hint : ∀ x, Integrable (fun u => f (x + μ • u)) (stdGaussian E)) :
    ConvexOn ℝ Set.univ (RandomGradFree.Shared.smoothing f μ) := by sorry

end RandomGradFree.Smooth
