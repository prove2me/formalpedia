-- Prove2me | Theorems.Thm_UCConvexHull_OneUC_theorem_1
-- name    : UCConvexHull.OneUC.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:16.34311+00:00
-- url     : https://prove2.me/theorems/04db5c6b-ddd0-4e4f-93d5-54fe79b452f7
-- title:
--   Theorem 1, pp. 18–19 — the relaxation of the DP formulation (26) is the closed convex hull of its mixed-integer points (1UC with ramping and convex cost)
-- statement:
--   Consider one thermal unit over the periods $T=\{1,\dots,n\}$ with minimum up and down times $\tau^\pm\ge 1$, initial state $\tau^0\ne 0$, output limits $l\le\bar l\le u$, $l\le\bar u\le u$, ramp limits $0\le\Delta^\pm\le u-l$, and a convex generation cost $f$. Let $G$ be its dynamic-programming state-space graph, $A_{ON}$ its set of ON arcs $(OFF_h,ON_k)$, and consider formulation (26):
--
--   $$\begin{aligned}
--   \min\ & \tilde c\,y+\sum_{(h,k)\in A_{ON}} z^{hk}\\
--   & Ey=\delta,\ \ y\ge 0 && (18)\\
--   & z^{hk}\ \ge\ \sum_{t\in T(h,k)} y^{hk}_+\,f\!\left(p^{hk}_t/y^{hk}_+\right) && (h,k)\in A_{ON},\\
--   & \text{(19) scaled by } y^{hk}_+,\ \ y^{hk}_+\in[0,1] && (h,k)\in A_{ON}.
--   \end{aligned}$$
--
--   Let $R$ be its constraint set in the space of $(y,(p^{hk},z^{hk})_{(h,k)\in A_{ON}})$, and let $S$ be the points of $R$ whose arc variables are all $0$ or $1$. Then
--
--   $$R=\overline{\operatorname{conv}}(S).$$
--
--   The continuous relaxation of (26) is exactly the closed convex hull of its mixed-integer points. Minimizing a linear objective over $R$ therefore solves the single-unit commitment problem with ramping constraints and a convex cost. The paper presents this as the first such convex-hull description.
--
--   **Formalization Note.**
--   1. "Describes the convex hull of the feasible solutions for (1UC)" is formalized in the extended space of (26): its mixed-integer points stand for the feasible solutions of (1UC). The paper's correspondence between $s$–$d$ paths of $G$ and feasible schedules of the 3-bin model (1)–(8) (§4, p. 14) is asserted without proof there and is not formalized.
--   2. The convex hull is closed, as in the paper's own convention $\overline{\operatorname{conv}}$ (Proposition 1, Lemma 1).
--   3. Dispatch blocks are attached to $A_{ON}$ only, as printed; the ON-type source and sink arcs are plain flow arcs.
--   4. Each power vector is indexed by $\{0,\dots,n\}$ with coordinates outside $T(h,k)$ fixed at $0$; $y\,f(p/y)$ at $y=0$ is read as $0$, which is correct because the scaled bounds force $p=0$ there.
--   5. The hypotheses $\tau^\pm\ge 1$ are added: they are minimum numbers of periods.
-- source:
--   Bacci, Frangioni, Gentile, Tavlaridis-Gyparakis, New MINLP Formulations for the Unit Commitment Problems with Ramping Constraints, manuscript submitted to Operations Research (PDF sha256 eee1c5a4…e224), pp. 18–19, Theorem 1, (26)

import Mathlib
import Definitions.Def_UCConvexHull_OneUC_Model

namespace UCConvexHull.OneUC

/-- Theorem 1 (pp. 18–19): for a thermal unit with ramping constraints and a convex cost, the
constraint set of formulation (26), with the arc variables relaxed to the continuous system (18), is
the closure of the convex hull of its mixed-integer points. -/
theorem theorem_1 (U : ThermalUnit) (hU : U.Standing) :
    relax U = closure (convexHull ℝ (mixedInt U)) := by sorry

end UCConvexHull.OneUC
