-- Prove2me | Theorems.Thm_UCConvexHull_OneUC_flowPoly_integral
-- name    : UCConvexHull.OneUC.flowPoly_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:13.310132+00:00
-- url     : https://prove2.me/theorems/d31fcd15-34e3-43c8-b5c7-85e239362455
-- title:
--   §5, p. 16 — the flow system (18) on the DP graph G has the integrality property: its polytope is the convex hull of its 0/1 points
-- statement:
--   Let a thermal unit satisfy the standing assumptions, and let $G$ be its dynamic-programming state-space graph (nodes $s$, $d$, $ON_t$, $OFF_t$; ON, OFF, source and sink arcs as in §4). Let $E$ be the node–arc incidence matrix of $G$ and $\delta$ the vector with $\delta_s=-1$, $\delta_d=1$ and zeros elsewhere. Then the polytope of (18) is the convex hull of its integral points:
--
--   $$\{\,y : Ey=\delta,\ y\ge 0\,\}=\operatorname{conv}\{\,y : Ey=\delta,\ y\ge 0,\ y\in\{0,1\}^A\,\}.$$
--
--   The $0/1$ points are the indicator vectors of the $s$–$d$ paths of $G$. This is why (18) alone would describe the convex hull of the single-unit problem if the objective were linear.
--
--   **Formalization Note.** The hypotheses $\tau^\pm\ge 1$ make $G$ acyclic, so the polytope is bounded and no closure is needed. With $\tau^+=\tau^-=0$, the arcs $(OFF_h,ON_{h-1})$ and $(ON_{h-1},OFF_h)$ would form a cycle.
-- source:
--   Bacci, Frangioni, Gentile, Tavlaridis-Gyparakis, New MINLP Formulations for the Unit Commitment Problems with Ramping Constraints, manuscript submitted to Operations Research (PDF sha256 eee1c5a4…e224), p. 16, §5, 'Separately, (18) has the integrality property' (printed as (??)); (18), p. 15

import Mathlib
import Definitions.Def_UCConvexHull_OneUC_Model

namespace UCConvexHull.OneUC

/-- §5, p. 16: the flow system (18) of the DP graph `G` has the integrality property — its polytope
is the convex hull of its `0/1` points. -/
theorem flowPoly_integral (U : ThermalUnit) (hU : U.Standing) :
    flowPoly U = convexHull ℝ {y | y ∈ flowPoly U ∧ ∀ e, y e = 0 ∨ y e = 1} := by sorry

end UCConvexHull.OneUC
