-- Prove2me | Theorems.Thm_UCConvexHull_OneUC_composition_hull
-- name    : UCConvexHull.OneUC.composition_hull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:13.524198+00:00
-- url     : https://prove2.me/theorems/600c546d-a34b-4398-881e-c0e527e5a2c2
-- title:
--   Proof of Theorem 1, p. 19 — (18) plus the dispatch blocks of any set J of ON arcs describes the closed convex hull of S_j (hull part)
-- statement:
--   Let a thermal unit satisfy the standing assumptions, and let $J\subseteq A_{ON}$ be any set of ON arcs of its DP graph. Let $R_J$ be the set of points $(y,(p^{hk},z^{hk})_{(h,k)\in A_{ON}})$ such that
--   1. $y$ satisfies the flow system (18), $Ey=\delta$, $y\ge 0$;
--   2. for every $(h,k)\in J$, $(y^{hk}_+,p^{hk},z^{hk})$ lies in the perspective dispatch block of $(h,k)$ (the constraints (19) scaled by $y^{hk}_+\in[0,1]$ and $z^{hk}\ge\sum_{t\in T(h,k)}y^{hk}_+f(p^{hk}_t/y^{hk}_+)$);
--   3. for every $(h,k)\notin J$, $p^{hk}=0$ and $z^{hk}=0$.
--
--   Let $S_J$ be the points of $R_J$ whose arc variables are all $0$ or $1$. Then
--
--   $$R_J=\overline{\operatorname{conv}}(S_J).$$
--
--   This is the induction of the proof of Theorem 1, which glues the dispatch blocks onto (18) one ON arc at a time. Taking $J=A_{ON}$ gives Theorem 1.
--
--   **Formalization Note.** The proof's further claim, that each intermediate formulation "satisfies strong duality for each objective function", is not part of this statement. The variables of pairs outside $J$ are fixed at $0$ so that both sides live in one space.
-- source:
--   Bacci, Frangioni, Gentile, Tavlaridis-Gyparakis, New MINLP Formulations for the Unit Commitment Problems with Ramping Constraints, manuscript submitted to Operations Research (PDF sha256 eee1c5a4…e224), p. 19, proof of Theorem 1

import Mathlib
import Definitions.Def_UCConvexHull_OneUC_Model

namespace UCConvexHull.OneUC

/-- Proof of Theorem 1, p. 19 (hull part): for every set `J` of ON pairs, the system (18) together
with the dispatch blocks of the pairs in `J` is the closure of the convex hull of its mixed-integer
points `S_j`. -/
theorem composition_hull (U : ThermalUnit) (hU : U.Standing) (J : Finset (onPairs U)) :
    relaxJ U J = closure (convexHull ℝ (mixedIntJ U J)) := by sorry

end UCConvexHull.OneUC
