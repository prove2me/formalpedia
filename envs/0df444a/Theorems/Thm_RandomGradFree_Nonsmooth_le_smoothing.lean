-- Prove2me | Theorems.Thm_RandomGradFree_Nonsmooth_le_smoothing
-- name    : RandomGradFree.Nonsmooth.le_smoothing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T07:48:38.797981+00:00
-- url     : https://prove2.me/theorems/d5ac0416-5398-4401-b509-7b8a4a8426c8
-- title:
--   Section 2, Eq. (11) — $f_\mu(x) \ge f(x)$ for convex $f$
-- statement:
--   Let $f : E \to \mathbb R$ be convex, let $\mu \ge 0$, and let $x \in E$ be a point at which the Gaussian average $\mathbb E_u f(x+\mu u)$ exists (is finite). Then
--
--   $$
--   f_\mu(x) = \mathbb E_u f(x+\mu u) \ge f(x).
--   $$
--
--   Gaussian smoothing therefore never lies below a convex function; combined with the $\mu L_0 n^{1/2}$ approximation bound, it sandwiches $f_\mu$ between $f$ and $f + \mu L_0 n^{1/2}$.
--
--   **Formalization Note** The paper's implicit assumption that $f_\mu(x)$ is finite is made explicit as integrability of $u \mapsto f(x+\mu u)$ against the standard Gaussian (without it the Bochner integral would be $0$ by convention); Lipschitz $f$ satisfies it. The subgradient $g \in \partial f(x)$ in the paper's display is a proof device, not a hypothesis.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 533, Section 2, Eq. (11)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Nonsmooth

theorem le_smoothing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E)
    (hint : Integrable (fun u => f (x + μ • u)) (stdGaussian E)) :
    f x ≤ RandomGradFree.Shared.smoothing f μ x := by sorry

end RandomGradFree.Nonsmooth
