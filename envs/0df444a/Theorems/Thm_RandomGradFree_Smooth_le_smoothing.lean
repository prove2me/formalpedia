-- Prove2me | Theorems.Thm_RandomGradFree_Smooth_le_smoothing
-- name    : RandomGradFree.Smooth.le_smoothing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T09:48:42.339991+00:00
-- url     : https://prove2.me/theorems/466232d4-2324-4193-9da7-50b9a8aee718
-- title:
--   Section 2, Eq. (11) — $f \le f_\mu$ for convex $f$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and $f : E \to \mathbb R$ convex. Then for every $\mu \ge 0$ and every $x \in E$ at which $f_\mu(x)$ is finite,
--
--   $$
--   f(x) \le f_\mu(x) = \mathbb E_u f(x + \mu u).
--   $$
--
--   Gaussian smoothing therefore never lies below a convex function; in the analysis of the random gradient method this converts a bound in terms of $f_\mu(x^*)$ into one in terms of $f(x^*)$ up to the approximation error.
--
--   **Formalization Note** The paper states (11) for convex $f$ with a subgradient $g \in \partial f(x)$ (which always exists for a finite convex function on $E$). The paper takes $f_\mu(x)$ to be well defined; the Lean statement makes this an explicit hypothesis, integrability of $u \mapsto f(x+\mu u)$ against the standard Gaussian, so the lower bound is on a genuine integral and never on the junk value $0$.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 533, Section 2, Eq. (11)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

theorem le_smoothing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E)
    (hint : Integrable (fun u => f (x + μ • u)) (stdGaussian E)) :
    f x ≤ RandomGradFree.Shared.smoothing f μ x := by sorry

end RandomGradFree.Smooth
