-- Prove2me | Theorems.Thm_ProximalBanach_Hybrid_prop5_three_point
-- name    : ProximalBanach.Hybrid.prop5_three_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:07:43.699744+00:00
-- url     : https://prove2.me/theorems/a3770cf3-b22c-4611-80cc-fe17a1f46b75
-- title:
--   Proposition 5 — φ(y, Q_C x) + φ(Q_C x, x) ≤ φ(y, x)
-- statement:
--   Let $E$ be a reflexive, strictly convex and smooth real Banach space with duality mapping $J$, let $C\subseteq E$ be nonempty, closed and convex, and let $x\in E$. Then
--   $$\varphi(y,Q_Cx)+\varphi(Q_Cx,x)\ \le\ \varphi(y,x)\qquad\text{for all } y\in C.\tag{2.6}$$
--
--   This is the Banach-space replacement for the Pythagorean inequality of the metric projection, and it produces the monotonicity (3.2) of $\varphi(x_n,x_0)$ along the algorithm.
--
--   **Formalization Note** The statement is made for any $q$ satisfying the defining property of $Q_Cx$ ($q\in C$ minimizing $\varphi(\cdot,x)$ over $C$); by Proposition 3 there is exactly one such $q$.
-- source:
--   Kamimura and Takahashi, Strong convergence of a proximal-type algorithm in a Banach space, SIAM J. Optim. 13(3), 2003, p. 941, Proposition 5, (2.6)

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Proposition 5 (p. 941): in a reflexive, strictly convex, smooth Banach space, for a
nonempty closed convex `C`, `x ∈ E` and `q = Q_C x`,
`φ(y, Q_C x) + φ(Q_C x, x) ≤ φ(y, x)` for all `y ∈ C` (2.6). -/
theorem prop5_three_point [StrictConvexSpace ℝ E] (hR : IsReflexive E) (hS : IsSmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x) (C : Set E)
    (hne : C.Nonempty) (hcl : IsClosed C) (hcv : Convex ℝ C) (x q : E)
    (hq : IsGenProj J C x q) :
    ∀ y ∈ C, phi J y q + phi J q x ≤ phi J y x := by sorry

end ProximalBanach.Hybrid
