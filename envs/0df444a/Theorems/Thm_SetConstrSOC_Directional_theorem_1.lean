-- Prove2me | Theorems.Thm_SetConstrSOC_Directional_theorem_1
-- name    : SetConstrSOC.Directional.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:24.224883+00:00
-- url     : https://prove2.me/theorems/b23f8aa6-b969-4021-8176-56705b9c7bb6
-- title:
--   Theorem 1 — primal second-order necessary condition
-- statement:
--   Let $\bar x$ be a locally optimal feasible solution of problem (P). For every $d\in T_F(\bar x)$ with $\nabla f(\bar x)d=0$ and every $w\in T_F^2(\bar x;d)$,
--
--   $$
--   \nabla f(\bar x)w+\nabla^2f(\bar x)(d,d)\ge0.
--   $$
--
--   This is the basic primal necessary condition used in the paper's directional dual result. The standing assumptions of (P) are retained.
-- source:
--   Gfrerer, Ye & Zhou, Second-order optimality conditions for non-convex set-constrained optimization problems, arXiv:1911.04076v2, p. 13, Theorem 1 (cf. [27, Corollary 1.3])

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model

namespace SetConstrSOC.Directional

/-- Theorem 1, p. 13: the primal second-order necessary condition. -/
theorem theorem_1 {n m : ℕ} (P : Problem n m) (hP : P.Standing)
    (x : E n) (hmin : IsLocalMinOn P.f P.feasible x) (hx : x ∈ P.feasible)
    (d : E n) (hd : d ∈ tangentCone P.feasible x)
    (hzero : (fderiv ℝ P.f x) d = 0) :
    ∀ w ∈ secondOrderTangentSet P.feasible x d,
      0 ≤ (fderiv ℝ P.f x) w + ((fderiv ℝ (fderiv ℝ P.f) x) d) d := by sorry

end SetConstrSOC.Directional
