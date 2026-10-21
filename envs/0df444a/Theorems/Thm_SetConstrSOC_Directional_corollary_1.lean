-- Prove2me | Theorems.Thm_SetConstrSOC_Directional_corollary_1
-- name    : SetConstrSOC.Directional.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:12.317322+00:00
-- url     : https://prove2.me/theorems/a268b280-3f45-4ba9-92a8-fa0e1fef3af5
-- title:
--   Corollary 1 — simultaneous nonemptiness of second-order tangent sets
-- statement:
--   Let $\bar x\in F$, and suppose that $g(x)-\Lambda$ is metrically subregular at $(\bar x,0)$ in direction $d$ with $\nabla g(\bar x)d\in T_\Lambda(g(\bar x))$. Then
--
--   $$
--   T_F^2(\bar x;d)\ne\varnothing
--   \quad\Longleftrightarrow\quad
--   T_\Lambda^2(g(\bar x);\nabla g(\bar x)d)\ne\varnothing.
--   $$
--
--   The result makes the nonemptiness assumption of Theorem 2 usable for the feasible second-order tangent set.
--
--   **Formalization Note** The printed $T_F^2(x;d)$ is read as $T_F^2(\bar x;d)$, as in its proof.
-- source:
--   Gfrerer, Ye & Zhou, Second-order optimality conditions for non-convex set-constrained optimization problems, arXiv:1911.04076v2, p. 12, Corollary 1

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model

namespace SetConstrSOC.Directional

/-- Corollary 1, p. 12: both second-order tangent sets are empty or nonempty together. -/
theorem corollary_1 {n m : ℕ} (P : Problem n m) (hP : P.Standing)
    (x d : E n) (hx : x ∈ P.feasible)
    (hMS : MetricSubregularDirAt P.g P.Λ x d)
    (hd : (fderiv ℝ P.g x) d ∈ tangentCone P.Λ (P.g x)) :
    (secondOrderTangentSet P.feasible x d).Nonempty ↔
      (secondOrderTangentSet P.Λ (P.g x) ((fderiv ℝ P.g x) d)).Nonempty := by sorry

end SetConstrSOC.Directional
