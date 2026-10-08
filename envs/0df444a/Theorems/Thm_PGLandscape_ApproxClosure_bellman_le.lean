-- Prove2me | Theorems.Thm_PGLandscape_ApproxClosure_bellman_le
-- name    : PGLandscape.ApproxClosure.bellman_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:33.935192+00:00
-- url     : https://prove2.me/theorems/de0b772c-96d2-4d11-bb6e-ee9a29615f13
-- title:
--   (5), p. 7 — element-wise Bellman inequalities TJ ⪯ T_π J and TJ_π ⪯ J_π
-- statement:
--   Let $\pi\in\Pi$ be a feasible stationary policy. For every bounded measurable function $J:S\to\mathbb R$, the Bellman optimality operator $T$ and the policy operator $T_\pi$ satisfy, at every state,
--
--   $$
--   TJ\preceq T_\pi J,\qquad\text{and}\qquad TJ_\pi\preceq J_\pi,
--   $$
--
--   where $J_\pi$ is the cost-to-go of $\pi$ and $\preceq$ is the element-wise order. These inequalities make the Bellman residual $J_\pi-TJ_\pi$ pointwise nonnegative, so its $L^1$ norm is its integral.
--
--   **Formalization Note** Both operators carry the discount factor $\gamma$: $(T_\pi J)(s)=g(s,\pi(s))+\gamma\int J\,dP(\cdot\mid s,\pi(s))$ and $TJ(s)=\inf_{a\in A_s}[g(s,a)+\gamma\int J\,dP(\cdot\mid s,a)]$. Displays (3) and (4) of the paper omit $\gamma$, while (6), (7), Assumption 2 and every proof use it. The page's "$J\in\mathcal J$" is read as bounded and measurable.
-- source:
--   arXiv:1906.01786v3, (5), p. 7

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.ApproxClosure

open MeasureTheory ProbabilityTheory

/-- (5), p. 7: `TJ ⪯ T_π J` for every bounded measurable `J`, and `TJ_π ⪯ J_π`, for `π ∈ Π`. -/
theorem bellman_le {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (π : PGLandscape.Closure.MPolicy S A) (hπ : PGLandscape.Closure.IsFeasible M π) :
    (∀ J : S → ℝ, Measurable J → (∃ C : ℝ, ∀ s, |J s| ≤ C) →
        ∀ s, PGLandscape.Closure.bellmanOpt M J s ≤ PGLandscape.Closure.bellmanPi M π.1 J s) ∧
      ∀ s, PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M π) s ≤ PGLandscape.Closure.costToGo M π s := by sorry

end PGLandscape.ApproxClosure
