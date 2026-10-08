-- Prove2me | Theorems.Thm_RelaxedPRS_Feas_prop_5_1_part3
-- name    : RelaxedPRS.Feas.prop_5_1_part3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:55.098693+00:00
-- url     : https://prove2.me/theorems/9c7d52e5-641d-4d47-8fa8-24d6808e1572
-- title:
--   Proposition 5.1 Part 3, p. 17 — prox_{γd²_C} = (1/(2γ+1)) I + (2γ/(2γ+1)) P_C
-- statement:
--   Let $C$ be a nonempty closed convex subset of a real Hilbert space $\mathcal H$ with metric projection $P_C$, and let $\gamma>0$. If $P$ is the proximal map of $\gamma d_C^2$, i.e. $P(x)$ minimises $y\mapsto d_C^2(y)+\frac{1}{2\gamma}\|y-x\|^2$ for every $x$, then for every $x\in\mathcal H$
--   $$
--   P(x)=\frac{1}{2\gamma+1}\,x+\frac{2\gamma}{2\gamma+1}\,P_C(x).
--   $$
--
--   This closed form drives the whole feasibility analysis: each prox step moves a point a fixed fraction of the way to its projection.
--
--   **Formalization Note** The prox map is any map satisfying the published `IsProx γ (d²_C) P`, with $d_C^2$ viewed as an extended-real function; the projection is a map satisfying `IsMetricProjection`.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 17, Proposition 5.1 Part 3

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_RelaxedPRS_Feas_Setting
open ThreeOpSplitting.ConvexRates RandomGradFree.Nonsmooth Filter Topology

namespace RelaxedPRS.Feas

/-- Proposition 5.1 Part 3, p. 17: for a nonempty closed convex `C` and `γ > 0`,
`prox_{γ d²_C} = (1/(2γ+1)) I_H + (2γ/(2γ+1)) P_C`. -/
theorem prop_5_1_part3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hC : IsClosed C) (hCv : Convex ℝ C) (hCne : C.Nonempty)
    (PC : H → H) (hPC : ∀ x, IsMetricProjection C x (PC x))
    (γ : ℝ) (hγ : 0 < γ) (P : H → H) (hP : IsProx γ (dsq C) P) :
    ∀ x : H, P x = (2 * γ + 1)⁻¹ • x + (2 * γ / (2 * γ + 1)) • PC x := by sorry

end RelaxedPRS.Feas
