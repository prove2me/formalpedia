-- Prove2me | Theorems.Thm_RelaxedPRS_Feas_prop_5_1_part2
-- name    : RelaxedPRS.Feas.prop_5_1_part2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:55.115876+00:00
-- url     : https://prove2.me/theorems/a24c9059-fb54-4acc-be94-45a1c9432230
-- title:
--   Proposition 5.1 Part 2, p. 17 — d²_C is differentiable, ∇d²_C = 2(I − P_C), and ∇d²_C is 2-Lipschitz
-- statement:
--   Let $C$ be a nonempty closed convex subset of a real Hilbert space $\mathcal H$, and let $P_C$ be the metric projection onto $C$ ($P_C(x)\in C$ and $\|x-P_C(x)\|\le\|x-w\|$ for all $w\in C$). Then the squared distance $d_C^2(x)=\left(\inf_{y\in C}\|x-y\|\right)^2$ is differentiable at every point, with
--   $$
--   \nabla d_C^2(x)=2\,(x-P_C(x)),
--   $$
--   and the gradient map $x\mapsto 2(x-P_C(x))$ is $2$-Lipschitz.
--
--   This gives the smoothness of $f=d^2_{C_f}$ and $g=d^2_{C_g}$ that lets the fundamental inequality of the paper (Proposition 1.2) be specialised to the feasibility problem.
--
--   **Formalization Note** Differentiability with gradient $2(I-P_C)$ is stated as `HasGradientAt` at every point; the projection is a map $P_C$ characterised by the published `IsMetricProjection` predicate.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 17, Proposition 5.1 Part 2

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_RelaxedPRS_Feas_Setting
open ThreeOpSplitting.ConvexRates RandomGradFree.Nonsmooth Filter Topology

namespace RelaxedPRS.Feas

/-- Proposition 5.1 Part 2, p. 17: for a nonempty closed convex `C`, `d²_C` is differentiable with
`∇d²_C = 2(I_H − P_C)`, and `∇d²_C` is 2-Lipschitz. `PC` is the metric projection onto `C`. -/
theorem prop_5_1_part2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hC : IsClosed C) (hCv : Convex ℝ C) (hCne : C.Nonempty)
    (PC : H → H) (hPC : ∀ x, IsMetricProjection C x (PC x)) :
    (∀ x : H, HasGradientAt (fun y => Metric.infDist y C ^ 2) ((2 : ℝ) • (x - PC x)) x) ∧
      LipschitzWith 2 (fun x : H => (2 : ℝ) • (x - PC x)) := by sorry

end RelaxedPRS.Feas
