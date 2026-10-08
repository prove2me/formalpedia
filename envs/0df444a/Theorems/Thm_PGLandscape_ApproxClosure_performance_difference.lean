-- Prove2me | Theorems.Thm_PGLandscape_ApproxClosure_performance_difference
-- name    : PGLandscape.ApproxClosure.performance_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:52.555805+00:00
-- url     : https://prove2.me/theorems/8a4082ca-7f53-41b1-9f67-dd4b2bb23654
-- title:
--   Equation (29), p. 39 — performance difference identity
-- statement:
--   For two feasible measurable stationary policies $\pi,\bar\pi\in\Pi$, the difference of their normalized discounted costs $\ell(\pi)=(1-\gamma)\int J_\pi\,d\rho$ is the Bellman residual of $J_{\bar\pi}$ under $\pi$, averaged against the discounted occupancy measure of $\pi$:
--
--   $$
--   \ell(\pi)-\ell(\bar\pi)=\int\bigl[T_\pi J_{\bar\pi}-J_{\bar\pi}\bigr]\,d\eta_\pi .
--   $$
--
--   This performance difference identity relates a comparison of whole trajectories to a one-step policy update.
--
--   **Formalization Note** The page's middle member (an expectation over the chain) has no object in this development and is omitted; the statement is the equality of the outer members. Both policies are required to be feasible, as on the page. $T_\pi$ carries the discount $\gamma$.
-- source:
--   arXiv:1906.01786v3, (29), p. 39

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.ApproxClosure

open MeasureTheory ProbabilityTheory

/-- (29), App. D.1, p. 39: `ℓ(π) − ℓ(π̄) = ∫ [T_π J_π̄ − J_π̄] dη_π`. -/
theorem performance_difference {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) (π πbar : PGLandscape.Closure.MPolicy S A)
    (hπ : PGLandscape.Closure.IsFeasible M π) (hπbar : PGLandscape.Closure.IsFeasible M πbar) :
    PGLandscape.Closure.loss M π - PGLandscape.Closure.loss M πbar =
      ∫ s, (PGLandscape.Closure.bellmanPi M π.1 (PGLandscape.Closure.costToGo M πbar) s - PGLandscape.Closure.costToGo M πbar s) ∂(PGLandscape.Closure.occupancy M π) := by sorry

end PGLandscape.ApproxClosure
