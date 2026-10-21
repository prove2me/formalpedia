-- Prove2me | Theorems.Thm_UCConvexHull_OneUC_block_hull
-- name    : UCConvexHull.OneUC.block_hull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:07.589846+00:00
-- url     : https://prove2.me/theorems/ff398d10-c4ff-4e13-9d8c-6396d2aa94a6
-- title:
--   (21), p. 16 — the perspective reformulation of (EED^{hk}) describes the closed convex hull of its feasible solutions
-- statement:
--   Let a thermal unit satisfy the standing assumptions, and let $(h,k)\in A_{ON}$ be an ON arc of the DP graph. Its dispatch block $B^{hk}_{21}$ is the set of $(y,p,z)$, with $y=y^{hk}_+$, $p=(p^{hk}_t)_{t\in T(h,k)}$ and one epigraph coordinate $z_t=z^{hk}_t$ for each period, such that $0\le y\le 1$, the constraints (19) hold with every bound multiplied by $y$, and
--
--   $$z_t\ \ge\ y\,f\!\left(p_t/y\right)\qquad(t\in T(h,k)).$$
--
--   Then $B^{hk}_{21}$ is the closure of the convex hull of its points with binary $y$:
--
--   $$B^{hk}_{21}=\overline{\operatorname{conv}}\{\,(y,p,z)\in B^{hk}_{21} : y\in\{0,1\}\,\}.$$
--
--   The points with $y=1$ are the feasible dispatches of (EED$^{hk}$) with period-wise epigraph variables; the points with $y=0$ have $p=0$ and every $z_t\ge 0$. This is the perspective reformulation of (21).
--
--   **Formalization Note.**
--   1. Lean reads $y\,f(p_t/y)$ at $y=0$ as $0\cdot f(0)=0$. This is the perspective's value there, because the scaled bounds force $p=0$ when $y=0$.
--   2. The power and epigraph vectors are indexed by $\{0,\dots,n\}$, with coordinates outside $T(h,k)$ fixed at $0$. The redundant aggregate inequality in the definition follows by summing the period-wise inequalities.
-- source:
--   Bacci, Frangioni, Gentile, Tavlaridis-Gyparakis, New MINLP Formulations for the Unit Commitment Problems with Ramping Constraints, manuscript submitted to Operations Research (PDF sha256 eee1c5a4…e224), p. 16, (21), with (19), p. 15

import Mathlib
import Definitions.Def_UCConvexHull_OneUC_Model

namespace UCConvexHull.OneUC

/-- (21), p. 16: for an ON arc `(h, k) ∈ A_ON`, the perspective dispatch block with one
epigraph variable `z_t` for each period is the closure of the convex hull of its points with
`y ∈ {0, 1}`. -/
theorem block_hull (U : ThermalUnit) (hU : U.Standing) (h k : ℕ) (hk : (h, k) ∈ onPairs U) :
    block21 U h k = closure (convexHull ℝ {q | q ∈ block21 U h k ∧ (q.1 = 0 ∨ q.1 = 1)}) := by sorry

end UCConvexHull.OneUC
